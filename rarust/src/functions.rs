use crate::{lp::{RType, ResourceVarId}, rich_type::RichType, scc};
/*  function signatures, 
    group(super node of call graph),
    function calling
*/

use charon_lib::{llbc_ast::{FunDecl, Statement}, types::Ty};
use im::vector;

use crate::lp::{FunIndex, GroupIndex, Lp, Resource};
use std::{collections::{HashMap, HashSet}, fmt};
#[derive(Debug, Clone)]
pub struct FunSig
{
    pub params : Vec<RType>, 
    pub ret : RType,
    pub delta : Resource,
}
impl fmt::Display for FunSig
{
    fn fmt(&self, f:&mut fmt::Formatter) -> fmt::Result
    {
        writeln!(f, "params:{:?}", self.params)?;
        writeln!(f, "ret:{:?}", self.ret)?;
        writeln!(f, "delta:{}", self.delta)
    }
}
#[derive(Debug, Clone)]
pub struct FunGroup /* group by call cycle */
{
    pub fun_sigs : HashMap<FunIndex, FunSig>,
    pub lp : Lp,
}
impl fmt::Display for FunGroup
{
    fn fmt(&self, f:&mut fmt::Formatter) -> fmt::Result
    {
        write!(f, "fun_sigs:[\n")?;
        for (findex, fun_sig) in self.fun_sigs.iter()
        {
            write!(f, "f_{findex} : {fun_sig},\n")?;
        }
        writeln!(f, "]")?;
        writeln!(f, "lp:{{{}}}", self.lp)
    }
}
#[derive(Debug, Clone)]
pub struct CallGraph
{
    pub fun_groups : Vec<FunGroup>,
    pub fun_group_indices : Vec<GroupIndex>, // findex -> gindex
}
impl fmt::Display for CallGraph
{
    fn fmt(&self, f:&mut fmt::Formatter) -> fmt::Result
    {
        write!(f, "fun_groups:[\n")?;
        for fun_group in self.fun_groups.iter()
        {
            write!(f, "{fun_group},\n")?;
        }
        writeln!(f, "]")
    }
}

#[derive(Debug)]
pub struct CallGraphBuilder
{
    pub nextss : Vec<HashSet<FunIndex>>,
    pub current_index : FunIndex,
}
impl CallGraphBuilder
{
    pub fn new(len:usize) -> CallGraphBuilder
    {
        CallGraphBuilder { nextss : vec![HashSet::new(); len], current_index:0 }
    }
    pub fn walk(&mut self, stmt:&Statement)
    {
        use charon_lib::llbc_ast::RawStatement::*;
        match &stmt.content
        {
        | Nop | FakeRead(_) | Return 
        | Break(_) | Continue(_) => (),
        | Drop(_p) => {}
        | Assign(_l, _r) => {}
        | Sequence(s1, s2) => {
            self.walk(s1); self.walk(s2);
        }
        | Switch(switch) => {
            use charon_lib::llbc_ast::Switch::*;
            match switch 
            {
            If(_, fst, snd) => {
                self.walk(fst); self.walk(snd);
            },
            SwitchInt(_, _, branches, default) => {
                for (_, stmt) in branches
                {
                    self.walk(stmt);
                }
                self.walk(&default);
            },
            Match(_, branches, default) => {
                for (_, stmt) in branches
                {
                    self.walk(stmt);
                }
                match default 
                {
                | Some(stmt) => self.walk(stmt),
                | None => ()
                }
            },
        }
        }
        | Call(call) => {
            use charon_lib::ullbc_ast::FnOperand::*;
            match &call.func
            {
            | Regular(fptr) => {
                use charon_lib::ullbc_ast::FunIdOrTraitMethodRef::*;
                match &fptr.func
                {
                | Fun(id) => {
                    use charon_lib::ullbc_ast::FunId::*;
                    match id 
                    { 
                    | Regular(id) => {
                        let callee_index = id.index;
                        let caller_index = self.current_index;
                        if callee_index < self.nextss.len()
                        { self.nextss[callee_index].insert(caller_index); }
                    },
                    | Assumed(id) => { // those primitive from stdlib
                        use charon_lib::ullbc_ast::AssumedFunId::*;
                        match id
                        {
                        | BoxNew => (),
                        | _ => todo!(), 
                        }
                    }, 
                    }
                },
                | Trait(_, _, _) => todo!(),
                }
            },
            | Move(_) => todo!("unsupport function pointer"),
            }
        },
        | Loop(stmt) => self.walk(stmt),
        | _stmt => unreachable!("unsupport"),
        }
    
    }
}


impl Lp
{
    /** enrich types of parameters of functions */
    fn enrich(&mut self, rtypedecls:&Vec<RType>, ty:&Ty) -> RType
    {
        use charon_lib::types::Ty::*;
        use charon_lib::types::TypeId;
        use RichType::*;
        match ty {
        | Literal(_) => Primitive,
        | Adt(tid, generic_args) => {
            match tid 
            {
            | TypeId::Adt(adt_id) => {
                let tindex = adt_id.index;
                let rtype = self.fresh_rtype(&rtypedecls[tindex]);
                rtype
            },
            | TypeId::Assumed(t) => {
                use charon_lib::types::AssumedTy::*;
                match t {
                | Box => {
                    let ty = &generic_args.types[0];
                    let rtype = self.enrich(rtypedecls, ty);
                    BoxOf(std::boxed::Box::new(rtype))    
                }
                | _ => unimplemented!("unsupport"),
                }
            },
            | TypeId::Tuple => {
                // Warning : no consideration for regions, trait_refs, ...
                let types = &generic_args.types;
                let rtypes = types.iter()
                    .map(|ty|{ self.enrich(rtypedecls, ty) })
                    .collect::<Vec<_>>();
                Tuple(rtypes, self.fresh())
            },
            }
        },
        | Ref(_region, ty, ref_kind) => {
            let rtype = self.enrich(rtypedecls, ty);
            use charon_lib::types::RefKind::*;
            match ref_kind
            {
            | Shared => RichType::Shared(Box::new(rtype)),
            | Mut => {
                let rtc = rtype;
                let rtp = self.fresh_rtype(&rtc);
                RichType::Mutable(Box::new(rtc), Box::new(rtp))
            },
            }
        },
        | _ => unimplemented!()
        }
    }
}
pub fn scc_analysis(rtypedecls:&Vec<RType>, functions:&Vec<FunDecl>) -> (Vec<FunGroup>, Vec<GroupIndex>)
{
    let funs_len = functions.len();
    let mut call_graph = CallGraphBuilder::new(funs_len);
    for (findex, func) in functions.iter().enumerate()
    {
        let Some(body) = &func.body else { continue };
        let stmt = &body.body;
        call_graph.current_index = findex;
        call_graph.walk(stmt);
    }
    let graph = scc::Graph { nodes : call_graph.nextss.into_iter().map(|nexts|{
        scc::Node { nexts : nexts.into_iter().collect::<Vec<_>>() }
    }).collect::<Vec<_>>() };
    let components = scc::make_top_sort(&graph);

    let fun_groups = components.iter().map(|component|{
        let mut lp = Lp { var_size:ResourceVarId(0), constraints:vector![], symbolics:im::HashSet::new() };
        let fun_sigs = component.iter().map(|findex|{
            let charon_lib::types::FunSig { inputs, output, .. } = &functions[*findex].signature;
            let params = inputs.iter().map(|ty|lp.enrich(rtypedecls, ty)).collect::<Vec<_>>();
            let ret = lp.enrich(rtypedecls, output);
            let delta = lp.fresh();
            let fun_sig = FunSig { params, ret, delta };
            (*findex, fun_sig)
        }).collect::<HashMap<_, _>>();
        FunGroup { fun_sigs, lp }
    }).collect::<Vec<_>>();
    let mut group_indices = vec![0; funs_len];
    for (gindex, component) in components.iter().enumerate()
    {
        for findex in component
        {
            group_indices[*findex] = gindex;
        }
    }
    let fun_group_indices = group_indices;

    (fun_groups, fun_group_indices)
}
