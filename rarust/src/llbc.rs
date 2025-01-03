use std::collections::HashMap;

use good_lp::{default_solver, variable, ProblemVariables, Solution, SolverModel};
use im::vector;
use serde::{Serialize, Deserialize};
use charon_lib::{llbc_ast::{FunDecl, GlobalDecl, TraitDecl, TraitImpl}, reorder_decls::DeclarationGroup, types::TypeDecl};
use charon_lib::meta::{FileId, FileName};

use crate::{constraint, functions::{scc_analysis, CallGraph, FunGroup, FunSig}, get_expr, lp::{Convertor, FunIndex, Lp, RType, Resource, ResourceVarId}, rich_type::RichType, typ_ctx::Gamma, typing::Context};
use crate::enrich::enrich_typedecls;
use crate::printer::Printer;

/// A generic crate, which implements the [Serialize] trait
#[derive(Debug, Serialize, Deserialize)]
pub struct LLBC
{
    pub name: String,
    /// The `id_to_file` map is serialized as a vector.
    /// We use this map for the spans: the spans only store the file ids, not
    /// the file names, in order to save space.
    pub id_to_file: Vec<(FileId::Id, FileName)>,
    pub declarations: Vec<DeclarationGroup>,
    pub types: Vec<TypeDecl>,
    pub functions: Vec<FunDecl>,
    pub globals: Vec<GlobalDecl>,
    pub trait_decls: Vec<TraitDecl>,
    pub trait_impls: Vec<TraitImpl>,
}
impl LLBC 
{
    pub fn handle(self, mut printer:Printer)
    {
        let mut fun_groups = self.traverse();
        for fun_group in fun_groups.iter_mut().skip(1) // skip rrlib.tick
        {
            let solution = fun_group.solve();
            printer.set_solution(solution);
            for findex in fun_group.fun_sigs.keys().map(|k|*k).collect::<Vec<FunIndex>>()
            {
                // if findex == tick_findex { continue; }
                let fun_sig = &fun_group.fun_sigs[&findex];
                let function = &self.functions[findex];
                printer.print_signature(&self.types, function, fun_sig).unwrap();
            }
        }
        
    }
}

impl LLBC
{
    fn traverse(self:&LLBC) -> Vec<FunGroup>
    {
        let rtypedecls = enrich_typedecls(&self.types);
        let (fun_groups, fun_group_indices) = scc_analysis(&rtypedecls, &self.functions);
        let call_graph = CallGraph { fun_groups: Vec::with_capacity(fun_groups.len()), fun_group_indices };

        let functions = &self.functions;
        let tick_findex = {
            use charon_lib::names::{Name, PathElem::Ident, Disambiguator};
            let tick_name = Name { name : vec![
                Ident(String::from("rrlib"), Disambiguator::Id::new(0)),
                Ident(String::from("tick"), Disambiguator::Id::new(0))
            ] };
            let mut tick_findex = functions.len()-1;

            for (findex, fun) in functions.iter().enumerate().rev()
            {
                // eprintln!("fun name = {:?}, findex = {findex}", fun.name); 
                if fun.name == tick_name { tick_findex = findex; break }
            }
            tick_findex
        };

        let gamma_placeholder = Gamma { rtypes:vector![] };
        let lp_placeholder = Lp { var_size: ResourceVarId(0), constraints: vector![], symbolics: im::HashSet::new() };
        let fun_group_placeholder = FunGroup { fun_sigs: HashMap::new(), lp: lp_placeholder };
        let mut context = Context { 
            rtypedecls,
            call_graph,
            gamma:gamma_placeholder, 
            gindex:0, 
            fun_group:fun_group_placeholder,
            tick_findex,
            looping:vec![],
        };
        for (gindex, group) in fun_groups.into_iter().enumerate()
        {
            context.fun_group = group;
            for findex in context.fun_group.fun_sigs.keys().map(|k|*k).collect::<Vec<FunIndex>>()
            {
                let Some(body) = &functions[findex].body else { break; };
                
                let fun_sig = context.fun_group.fun_sigs[&findex].clone();
                let rtypes = {
                    let params = &fun_sig.params;
                    let ret = &fun_sig.ret;
                    (0..body.locals.len()).map(|id|{
                        if id==0 { ret.clone() }
                        else if id <= params.len() { params[id-1].clone() }
                        else { RichType::Undefined }
                    }).collect::<im::Vector<_>>()
                };
                
                context.gindex = gindex;
                context.gamma = Gamma { rtypes };            

                let stmt = &body.body;
                let (delta, new_context) = context.exec(stmt);
                let Context{rtypedecls, call_graph, mut fun_group, gamma, gindex, tick_findex, looping } = new_context;
                fun_group.lp.add(constraint!(fun_sig.delta.clone() >= delta));
                
                // sig_ret <= exec_ret
                fun_group.lp.prec(&fun_sig.ret, &gamma.rtypes[0]);
                context = Context{ rtypedecls, call_graph, fun_group, gindex, gamma, tick_findex, looping };
            }
            context.call_graph.fun_groups.push(context.fun_group);
        }
        context.call_graph.fun_groups

    }
}

impl Convertor
{
    fn rtype(&self, rtype:&RType) -> good_lp::Expression
    {
        use RichType::*;
        match rtype
        {
        | Undefined => 0.into(),
        | Primitive => 0.into(),
        | Tuple(rfields, r) => {
            rfields.iter().fold(self.resource(r) , |r_sum, rtype|{
                match rtype
                {
                | BoxOf(_rt) => r_sum,
                | _ => r_sum + self.rtype(rtype)
                }
            })
        },
        | Variant(rvariants) => {
            rvariants.iter()
            .fold(0.into(), |r_sum, (rfields, r)|{
                let r_sum = rfields.iter().fold(r_sum , |r_sum, rtype|{
                    match rtype
                    {
                    | BoxOf(_rt) => r_sum,
                    | _ => r_sum + self.rtype(rtype)
                    }
                });
                let rec_times = rfields.iter().fold(0, |rec_times, rtype|{
                    match rtype
                    {
                    | BoxOf(rt) => {
                        let rt : &RType = rt;
                        match rt 
                        {
                        | SS(_) => rec_times + 1,
                        | _ => rec_times,
                        }
                    }
                    | _ => rec_times,
                    }
                });
                r_sum + (rec_times * 1000 + 1) * self.resource(r) 
            })
        },
        | SS(_) => 0.into(),
        | MR(_, rtype)
        | BoxOf(rtype)
        | Shared(rtype)
            => self.rtype(&rtype),
        | Mutable(rtc, _rtp) 
            => self.rtype(&rtc), // - self.rtype(&rtp)
        }
    }
}
impl FunGroup
{
    fn solve(&mut self) -> Vec<f64>
    {
        // self.constraints
        let mut vars = ProblemVariables::new();
        let variables = (0..self.lp.var_size.0+1).map(|_|{vars.add(variable().min(0))}).collect::<Vec<_>>();
        let _zero = variables[0].clone();
        let convertor = Convertor { variables };
        
        let mut objective : good_lp::Expression = 0.into();
        for fun_sig in self.fun_sigs.values()
        {
            let FunSig { params, ret, delta} = fun_sig;
            
            for param in params.iter()
            {
                objective = objective + convertor.rtype(param);
            }
            
            // NOTE : + ret
            objective = objective + convertor.rtype(ret);
            objective = objective + 2 * convertor.resource(delta);
        }
        /* 
        eprintln!("DEBUG obj = {:?}", objective);
        for (_, fun_sig) in self.fun_sigs.iter()
        {
            eprint!("{}", fun_sig);
        }
        for c in self.lp.constraints.iter()
        {
            eprintln!("{:?}", convertor.constraint(c) );
        }
        */
        
        let problem = vars.minimise(objective).using(default_solver);
        let problem = self.lp.constraints.iter()
            .fold(problem, |p, c|{
                p.with(convertor.constraint(c))
            });
        let Ok(solution) = problem.solve() else 
        {
            unimplemented!("no solution")
        };
        
        let solution = convertor.variables.into_iter().map(|v|{ solution.value(v) }).collect::<Vec<_>>();
        // eprintln!("solution = {:?}", solution);
        solution
        /* 
        for c in self.lp.constraints.iter()
        {
            // eprintln!("{:?}",convertor.constraint(c) );
        }
        for fun_sig in self.fun_sigs.values()
        {
            let FunSig { params, ret, delta} = fun_sig;
            for (i, v) in convertor.variables.iter().enumerate()
            {
                // println!("v{i} = {}", solution.value(*v));
            }
            print!("Complexity = ");
            for (i, (param, param_out)) in std::iter::zip(params.iter().iter()).enumerate()
            {
                print!("{}n_{}+", solution.eval(convertor.rtype(param)-convertor.rtype(param_out)), i);
            }
            println!("{} ~> {}n_ret" , solution.eval(convertor.resource(delta)), solution.eval(convertor.rtype(ret)));
        }
        */
    }
}