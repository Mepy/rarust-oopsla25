use std::collections::HashSet;

use charon_lib::gast::{ConstantExpr, FieldProjKind, Operand, Rvalue};
use charon_lib::types::TypeId;
use charon_lib::llbc_ast::{Place, Statement};

use crate::lp::{FunIndex, GroupIndex, RType, Resource};
use crate::rich_type::{unfold, RichType};
use crate::typ_ctx::Gamma;
use crate::functions::{CallGraph, FunGroup, FunSig};


pub struct Context
{
    pub tick_findex : FunIndex,
    pub gamma : Gamma,
    pub call_graph : CallGraph,
    pub rtypedecls : Vec<RType>,

    // current walking function group
    pub gindex : GroupIndex,
    pub fun_group : FunGroup,

    // loop support
    pub looping : Vec<(Gamma, Resource)>, // (gamma, delta)
}

impl Context
{
    fn eval_operand(&mut self, operand:&Operand) -> RType
    {
        use Operand::*;
        match operand
        {
        | Const(ConstantExpr{ty:charon_lib::types::Ty::Literal(_), ..})
        | Copy(_) =>RichType::Primitive,
        | Const(ConstantExpr{ty:_, ..})
            => unimplemented!("no support for non literal constant"),
        | Move(place) => {
            let rtype = self.gamma.read(place);
            // eprintln!("Move {place:?} {rtype:?}");
            // todo: maybe we need NOT write undefined here
            // we write undefined only for local convenience of soundness proof
            // in practical implementation, we will recover soundness globally(across some eval/exec)
            
            // self.gamma.write(place, RichType::Undefined);
            rtype
        },
        }
    }
    fn share(&mut self, rtype:RType) -> (RType, RType)
    {
        use RichType::*;
        match rtype
        {
        | Undefined => (Undefined, Undefined),
        | Primitive => (Primitive, Primitive),
        | BoxOf(rt) => {
            let (rt1, rt2) = self.share(*rt);
            (BoxOf(Box::new(rt1)), BoxOf(Box::new(rt2)))
        },
        | Tuple(rfields, r) => {
            let (r1, r2) = self.fun_group.lp.split(r);
            let (rfields1, rfields2) : (Vec<_>, Vec<_>)= rfields.into_iter().map(|rt|{ self.share(rt) }).unzip();
            (Tuple(rfields1, r1), Tuple(rfields2, r2))
        }
        | Variant(rvariants) => {
            let (rvariants1, rvariants2) : (Vec<_>, Vec<_>) = rvariants.into_iter().map(|(rfields, r)|{
                let (r1, r2) = self.fun_group.lp.split(r);
                let (rfields1, rfields2) : (Vec<_>, Vec<_>)= rfields.into_iter().map(|rt|{ self.share(rt) }).unzip();
                ((rfields1, r1), (rfields2, r2))
            }).unzip();
            (Variant(rvariants1), Variant(rvariants2))
        },
        | SS(tindex) => (SS(tindex), SS(tindex)),
        | MR(tindex, rt) => {
            let (rt1, rt2) = self.share(*rt);
            (MR(tindex, Box::new(rt1)), MR(tindex, Box::new(rt2)))
        }
        | Shared(rt) => {
            let (rt1, rt2) = self.share(*rt);
            (Shared(Box::new(rt1)), Shared(Box::new(rt2)))
        },
        | Mutable(_, _) => unreachable!("can NOT share mutable borrows"), 
        }
    }
    fn eval(&mut self, expr:&Rvalue) -> (Resource, RType)
    {
        use Rvalue::*;
        match expr
        {
        | Use(operand)
        | UnaryOp(_, operand) 
        | BinaryOp(_, operand, _)
            => (Resource::Const(0.), self.eval_operand(operand)),
        | Aggregate(kind, ops) => {
            use charon_lib::ullbc_ast::AggregateKind::*;
            match kind
            {
            | Adt(tid, variant_id, _generic_args) => {
                match tid 
                {
                | TypeId::Adt(adt_id) => {
                    use RichType::*;
                    let rtypedecl = &self.rtypedecls[adt_id.index];
                    let rtype = self.fun_group.lp.fresh_rtype(rtypedecl);
                    match &rtype
                    {
                    | Tuple(rfields, r) => {
                        for (field_id, rt) in rfields.iter().enumerate()
                        {
                            let BoxOf(rt0) = rt else { continue; };
                            let rt0 : &RType = rt0;
                            match rt0
                            {
                            | SS(tindex) if *tindex == adt_id.index => {
                                let operand = &ops[field_id];
                                let BoxOf(rtype_op) = self.eval_operand(operand) else { unreachable!() };
                                self.fun_group.lp.prec(&rtype, &rtype_op);
                            },
                            | _ => {},
                            }
                        }
                        (r.clone(), rtype)
                    }
                    | Variant(rvariants) => {
                        let Some(variant_id) = variant_id else { unreachable!() };
                        let (rfields, _) = &rvariants[variant_id.index];
                        for (field_id, rt) in rfields.iter().enumerate()
                        {
                            let BoxOf(rt0) = rt else { continue; };
                            let rt0 : &RType = rt0;
                            match rt0
                            {
                            | SS(tindex) if *tindex == adt_id.index => {
                                let operand = &ops[field_id];
                                let BoxOf(rtype_op) = self.eval_operand(operand) else { unreachable!() };
                                self.fun_group.lp.prec(&rtype, &rtype_op);
                            },
                            | _ => {},
                            }
                        }
                        let Variant(rvariants) = &rtype else { unreachable!() };
                        let r = rvariants[variant_id.index].1.clone();
                        
                        (r, rtype)
                    }
                    | MR(outer, outer_rtype) => {
                        let outer = *outer;
                        let outer_rtype : &RType = outer_rtype;
                        match outer_rtype
                        {
                        | Tuple(rfields, r) => {
                            for (field_id, rt) in rfields.iter().enumerate()
                            {
                                let rt = if let BoxOf(rt) = rt { rt } else { rt };
                                match rt
                                {
                                | MR(inner, inner_rtype)=> {
                                    let inner = *inner;
                                    let operand = &ops[field_id];
                                    let rtype_op = self.eval_operand(operand);
                                    let rtype_op = if let BoxOf(rtype_op) = rtype_op { *rtype_op } else { rtype_op };

                                    let mut inner_rtype = *inner_rtype.clone();
                                    unfold(&mut inner_rtype, outer, outer_rtype);
                                    let unfolded_rtype = MR(inner, Box::new(inner_rtype));
                                    // eprintln!("compare {unfolded_rtype:?} {rtype_op:?}");
                                    self.fun_group.lp.prec(&unfolded_rtype, &rtype_op);
                                },
                                | _ => {},
                                }
                            }
                            (r.clone(), rtype)
                        }
                        | Variant(rvariants) => {
                            let Some(variant_id) = variant_id else { unreachable!() };
                            let (rfields, _) = &rvariants[variant_id.index];
                            for (field_id, rt) in rfields.iter().enumerate()
                            {
                                let rt = if let BoxOf(rt) = rt { rt } else { rt };
                                match rt
                                {
                                | MR(inner, inner_rtype)=> {
                                    let inner = *inner;
                                    let operand = &ops[field_id];
                                    let rtype_op = self.eval_operand(operand);
                                    let rtype_op = if let BoxOf(rtype_op) = rtype_op { *rtype_op } else { rtype_op };

                                    let mut inner_rtype = *inner_rtype.clone();
                                    unfold(&mut inner_rtype, outer, outer_rtype);
                                    let unfolded_rtype = MR(inner, Box::new(inner_rtype));
                                    // eprintln!("compare {unfolded_rtype:?} {rtype_op:?}");
                                    self.fun_group.lp.prec(&unfolded_rtype, &rtype_op);
                                },
                                | _ => {},
                                }
                            }
                            let r = rvariants[variant_id.index].1.clone();
                            
                            (r, rtype)
                        }
                        | _ => { unreachable!() }
                        }
                        
                    }
                    | _ => { unreachable!() }
                    }
                },
                | TypeId::Assumed(t) => {
                    use charon_lib::types::AssumedTy::*;
                    match t {
                    | Box => {
                        let operand = &ops[0];
                        let rtype = self.eval_operand(operand);
                        (Resource::Const(0.), rtype)
                    }
                    | _ => unimplemented!(),
                    }
                }
                | TypeId::Tuple => {
                    let rtypes = ops.iter().map(|op|{ self.eval_operand(op) }).collect::<Vec<_>>();
                    (Resource::Const(0.), RichType::Tuple(rtypes, self.fun_group.lp.fresh()))
                },
                }
            },
            | _ => unimplemented!(),
            }
        
        }
        | Ref(place, kind) => {
            use charon_lib::gast::BorrowKind::*;
            match kind
            {
            | Shared => {
                let rtype = self.gamma.read(place);
                let (rt1, rt2) = self.share(rtype);
                self.gamma.write(place, rt1);
                (Resource::Const(0.), RichType::Shared(Box::new(rt2)))
            }
            | TwoPhaseMut | Mut => {
                let rtc = self.gamma.read(place);
                let rtp = self.fun_group.lp.fresh_rtype(&rtc); // rich_type prophecy
                self.gamma.write(place, rtp.clone());
                (Resource::Const(0.), RichType::Mutable(Box::new(rtc), Box::new(rtp)))
            }
            | Shallow => unimplemented!("unsupport"),
            }
        }
        | Discriminant(_, _)
        | Global(_)
        | Len(_, _, _)
        | Repeat(_, _, _) 
            => unimplemented!("unsupport")
        }
    }
}

impl Context
{
    /** match place with | Tag => stmt */
    fn hack_adt_proj<'a>(&mut self, place:&Place, stmt:&'a Statement) -> &'a Statement
    {  
        use charon_lib::llbc_ast::RawStatement::*;
        use charon_lib::llbc_ast::Rvalue::*;
        use charon_lib::gast::BorrowKind::*;
        let mut cursor = stmt;

        // first peak is_adt_proj and borrow kind
        let Sequence(s1, _s2) = &cursor.content else { return cursor; };
        let Assign(_left_place, Ref(right_place, kind)) = &s1.content else { return cursor; };
        let is_adt_proj = {
            let mut flag = false;
            use charon_lib::ullbc_ast::ProjectionElem::*;
            let Place{ projection, .. } = right_place;
            for proj in projection
            {
                match proj
                {
                | Field(FieldProjKind::Adt(_, _), _) => { flag = true; break; }
                | _ => { continue; }
                }
            }
            flag
        };
        if is_adt_proj == false { return cursor; }

        match kind 
        {
        | Shared => {
            let rtype = self.gamma.read(place);
            let (rt1, rt2) = self.share(rtype); 
            // we always use rt2 to project
            loop 
            {
            let Sequence(s1, s2) = &cursor.content else { break; };
            let Assign(left_place, Ref(right_place, _kind)) = &s1.content else { break; };
            let is_adt_proj = {
                let mut flag = false;
                use charon_lib::ullbc_ast::ProjectionElem::*;
                let Place{ projection, .. } = right_place;
                for proj in projection
                {
                    match proj
                    {
                    | Field(FieldProjKind::Adt(_, _), _) => { flag = true; break; }
                    | _ => { continue; }
                    }
                }
                flag
            };
            if is_adt_proj == false { break; }
            self.gamma.write(place, rt2.clone()); // place := rt2, then left := right will project rt2
            let right_rtype = self.gamma.read(right_place);
            let (_, right_rt2) = self.share(right_rtype);
            self.gamma.write(left_place, RichType::Shared(Box::new(right_rt2)));
            cursor = s2; // continue to process
            } // end loop

            self.gamma.write(place, rt1); // restore rt1
        }
        | TwoPhaseMut | Mut => {
            let rtc = self.gamma.read(place);
            let rtp = self.fun_group.lp.fresh_rtype(&rtc); // rich_type prophecy
            // we always use (rtc, rtp) to project
            loop 
            {
            let Sequence(s1, s2) = &cursor.content else { break; };
            let Assign(left_place, Ref(right_place, _kind)) = &s1.content else { break; };
            let is_adt_proj = {
                let mut flag = false;
                use charon_lib::ullbc_ast::ProjectionElem::*;
                let Place{ projection, .. } = right_place;
                for proj in projection
                {
                    match proj
                    {
                    | Field(FieldProjKind::Adt(_, _), _) => { flag = true; break; }
                    | _ => { continue; }
                    }
                }
                flag
            };
            if is_adt_proj == false { break; }
            self.gamma.write(place, rtc.clone()); // place := rtc, then left := right will project rtc
            let right_rtc = self.gamma.read(right_place);
            self.gamma.write(place, rtp.clone()); // place := rtp, then left := right will project rtp
            let right_rtp = self.gamma.read(right_place);

            self.gamma.write(left_place, RichType::Mutable(Box::new(right_rtc), Box::new(right_rtp)));
            cursor = s2; // continue to process
            } // end loop

            self.gamma.write(place, rtp); // restore rtp
        }
        | Shallow => unimplemented!("unsupport")
        }
        
        cursor

    }
    pub fn exec(mut self, stmt:&Statement) -> (Resource, Context)
    {
        use charon_lib::llbc_ast::RawStatement::*;
        match &stmt.content
        {
        | Nop | FakeRead(_) => (Resource::Const(0.), self),
        | Return => {
            for rtype in self.gamma.rtypes.iter()
            {
                self.fun_group.lp.wf(rtype);
            }
            (Resource::Const(0.), self)
        },
        | Sequence(s1, s2) => {
            let (delta1, context) = self.exec(&s1);
            let (delta2, context) = context.exec(&s2);
            (delta1+delta2, context)
        },
        | Assign(place, expr) => {
            self.fun_group.lp.wf(&self.gamma.read(place)); // well form the old

            let (delta, rtype) = self.eval(&expr);
            self.gamma.write(place, rtype);
            (delta, self)
        },
        | Drop(place) => {
            let rtype = self.gamma.read(place);
            self.fun_group.lp.wf(&rtype);
            use RichType::*;
            match rtype
            {
            | Shared(_) => {
                self.gamma.write(place, Undefined);
                (Resource::Const(0.), self)
            }
            | Mutable(rtc, rtp) => {
                self.gamma.write(place, Undefined);
                self.fun_group.lp.prec(&rtp, &rtc);
                (Resource::Const(0.), self)
            }
            | _ => (Resource::Const(0.), self),
            // | _ => unreachable!("drop non borrows place={:?}, rtype={:?}", place, rtype)
            }
        },
        | Switch(switch) => {
            use charon_lib::llbc_ast::Switch::*;
            match switch 
            {
            | SwitchInt(_, _, _, _) => unimplemented!("no support for int"),
            | If(_cond, fst, snd) => {
                
                let gamma_pack = self.gamma.clone();
                let context = self;
                let (delta1, mut context) = context.exec(fst);
                let gamma1 = context.gamma;
                context.gamma = gamma_pack;
                let (delta2, mut context) = context.exec(snd);
                let gamma2 = context.gamma;
                let gamma = context.fun_group.lp.wedge(gamma1, gamma2);
                context.gamma = gamma;
                let delta = context.fun_group.lp.max(delta1, delta2);
                (delta, context)
            },
            | Match(place, branches, default) => {
                let rtype = self.gamma.read(place);
                // considering rtp or not
                // let rtp = self.fun_group.lp.fresh_rtype(&rtype); // prophecy for resource increase!
                // self.gamma.write(place, rtp);
                let rtype = match rtype {
                    | RichType::MR(_, rtype) => *rtype, 
                    | rtype => rtype,
                };
                let RichType::Variant(rvariants) = rtype else { unreachable!() };
                let gamma_pack = self.gamma.clone();
                if let Some(default_stmt) = default {
                    let mut deltas : Vec<Resource> = Vec::with_capacity(branches.len()+2);
                    // deltas.push(Resource::Const(0.)); 
                    // TODO : delete this, no need, all variables are >= 0
                    // only for debugging : to see the final delta >= all deltas
                    // we can clearly see that delta >= 0
                    let mut gamma = gamma_pack.clone(); // final gamma
                    let mut context = self;
                    let mut non_default_ids : HashSet<usize> = HashSet::with_capacity(2*branches.len());
                    for (ids, stmt) in branches
                    {
                        let rs = ids.iter().map(|id|{ 
                            non_default_ids.insert(id.index);
                            rvariants[id.index].1.clone() // (rfields, r)
                        }).collect::<Vec<_>>();
                        let r = context.fun_group.lp.mins(rs);
                        let stmt = context.hack_adt_proj(place, stmt);
                        let (delta, ctx) = context.exec(stmt);
                        context = ctx;
                        let RichType::Variant(beta) = context.gamma.read(place) else { unreachable!() };
                        let bs = ids.iter().map(|id|{ 
                            beta[id.index].1.clone() // (rfields, r)
                        }).collect::<Vec<_>>();
                        let b = context.fun_group.lp.maxs(bs);
                        let delta = delta-r+b;
                        context.fun_group.lp.add(constraint!(Resource::Const(0.) <= delta.clone()));
                        deltas.push(delta);
                        gamma = context.fun_group.lp.wedge(gamma, context.gamma);
                        context.gamma = gamma_pack.clone();
                    }

                    let default_rs = (0..rvariants.len()).filter_map(|id|{
                        if non_default_ids.contains(&id) { None }
                        else { Some(rvariants[id].1.clone()) }
                    }).collect::<Vec<_>>();
                    let default_r = context.fun_group.lp.mins(default_rs);
                    
                    let default_stmt = context.hack_adt_proj(place, &default_stmt);
                    let (default_delta, default_ctx) = context.exec(default_stmt);
                    context = default_ctx;
                    let RichType::Variant(beta) = context.gamma.read(place) else { unreachable!() };
                    let bs = (0..rvariants.len()).filter_map(|id|{
                        if non_default_ids.contains(&id) { None }
                        else { Some(beta[id].1.clone()) } // (rfields, r)
                    }).collect::<Vec<_>>();
                    let b = context.fun_group.lp.maxs(bs);
                    
                    let delta = default_delta-default_r+b;
                    context.fun_group.lp.add(constraint!(Resource::Const(0.) <= delta.clone()));
                    deltas.push(delta);
                    gamma = context.fun_group.lp.wedge(gamma, context.gamma);
                    let delta = context.fun_group.lp.maxs(deltas);
                    context.gamma = gamma;
                    (delta, context)
                }
                else 
                {
                    let mut deltas : Vec<Resource> = Vec::with_capacity(branches.len()+1);
                    // deltas.push(Resource::Const(0.));
                    let mut gamma = gamma_pack.clone(); // final gamma
                    let mut context = self;
                    for (ids, stmt) in branches
                    {
                        let rs = ids.iter().map(|id|{ 
                            rvariants[id.index].1.clone() // (rfields, r)
                        }).collect::<Vec<_>>();
                        let r = context.fun_group.lp.mins(rs);
                        let stmt = context.hack_adt_proj(place, stmt);
                        let (delta, ctx) = context.exec(stmt);
                        context = ctx;
                        // remember to copy to default = Some!!
                        let rtype = context.gamma.read(place);
                        let rtype = match rtype {
                            | RichType::MR(_, rtype) => *rtype, 
                            | rtype => rtype,
                        };
                        let RichType::Variant(beta) = rtype else { unreachable!() };
                        let bs = ids.iter().map(|id|{ 
                            beta[id.index].1.clone() // (rfields, r)
                        }).collect::<Vec<_>>();
                        let b = context.fun_group.lp.maxs(bs);
                        /* TODO : shall we just update at place?
                        eprintln!("DEBUG R := {r:?}");
                        eprintln!("DEBUG B := {b:?}");
                        eprintln!("DEBUG delta := {delta:?}");
                        */
                        let delta = delta-r+b;
                        context.fun_group.lp.add(constraint!(Resource::Const(0.) <= delta.clone()));
                        deltas.push(delta);
                        gamma = context.fun_group.lp.wedge(gamma, context.gamma);
                        
                        context.gamma = gamma_pack.clone();
                    }
                    let delta = context.fun_group.lp.maxs(deltas);
                    context.gamma = gamma;
                    (delta, context)
                }  
            },
            }
        }
        | Call(call) => {
            use charon_lib::ullbc_ast::FnOperand::*;
            match &call.func
            {
            | Move(_) => unimplemented!("unsupport function pointer"),
            | Regular(fptr) => {
                use charon_lib::ullbc_ast::FunIdOrTraitMethodRef::*;
                match &fptr.func
                {
                | Trait(_, _, _) => unimplemented!("unsupport trait"),
                | Fun(id) => {
                    use charon_lib::ullbc_ast::FunId::*;
                    match id 
                    {
                    | Assumed(id) => { // those primitive from stdlib
                        use charon_lib::ullbc_ast::AssumedFunId::*;
                        match id
                        {
                        | BoxNew => {
                            let Operand::Move(place) = &call.args[0] else { unreachable!() };
                            let rtype = self.gamma.read(place);
                            self.gamma.write(&call.dest, RichType::BoxOf(Box::new(rtype)));

                            (Resource::Const(0.), self)
                        }
                        | _ => todo!(), 
                        }
                    }, 
                    | Regular(id) => {
                        let callee_findex = id.index;
                        if callee_findex == self.tick_findex // hack rrlib::tick
                        {
                            use charon_lib::expressions::RawConstantExpr::Literal;
                            use charon_lib::values::{Literal::Scalar, ScalarValue::{Isize, I8, I16, I32, I64, I128}};
                            let Operand::Const(ConstantExpr{value:Literal(Scalar(q)), ..}) = call.args[0]
                            else { panic!("not constant argument for rrlib::tick")};
                            let q = match q 
                            { 
                            | Isize(q) => q as f64,
                            | I8(q) => q as f64,
                            | I16(q) => q as f64,
                            | I32(q) => q as f64,
                            | I64(q) => q as f64,
                            | I128(q) => q as f64, 
                            | _ => { panic!("not integer argument for rrlib::tick")}
                            };
                            (Resource::Const(q), self)

                        }
                        else {
                        let callee_gindex = self.call_graph.fun_group_indices[callee_findex];
                        let callee_sig = if callee_gindex == self.gindex // in the same strongly connect component
                        { self.fun_group.fun_sigs[&callee_findex].clone() }
                        else // instantiate lp
                        {
                            let callee_group = &self.call_graph.fun_groups[callee_gindex];
                            let caller_group = &mut self.fun_group;

                            let callee_lp = &callee_group.lp;
                            let caller_lp = &mut caller_group.lp;
                            let lifter = crate::lp::Lifter { offset : caller_lp.var_size.0 };
                            caller_lp.var_size.0 += callee_lp.var_size.0;
                            for constraint in callee_lp.constraints.iter()
                            {
                                caller_lp.constraints.push_back(lifter.constraint(constraint));
                            }
                            let FunSig{params, ret, delta} = &callee_group.fun_sigs[&callee_findex];
                            let params = params.iter().map(|rtype|{ lifter.rtype(rtype) }).collect();
                            let ret = lifter.rtype(&ret);
                            let delta = lifter.resource(&delta);
                            let callee_sig = FunSig { params, ret, delta };
                            callee_sig
                        };
                        let FunSig{params, ret, ..} = callee_sig;
                        self.gamma.write(&call.dest, ret.clone());
                        for (arg, param) in std::iter::zip(call.args.iter(), params.clone().into_iter())
                        {
                            let rarg = self.eval_operand(arg);
                            self.fun_group.lp.prec(&param, &rarg);
                            // self.fun_group.lp.eq(&param, &rarg);
                            /* 
                                We write prec instead of eq in formalization
                                and prec is also sound, 
                                prec is just to compromise phi(_:rarg-param) >= 0
                             */
                        }

                        let FunSig { delta, .. } = callee_sig;
                        
                        (delta, self)
                        }
                    },
                    }
                },
                }
            },
            }
        },
        | Loop(body) => {
            // eprintln!("LOOP gamma = {:?}", self.gamma);
            let delta = self.fun_group.lp.fresh();
            let mut context = self;
            context.looping.push((context.gamma.clone(), delta.clone()));
            let (r, mut context) = context.exec(&body);
            context.fun_group.lp.add(constraint!(r <= delta.clone()));
            context.looping.pop();
            (delta, context)
        }
        | Continue(i) => {
            let dbi = *i; // De Bruijn Index
            let len = self.looping.len();
            assert!(dbi < len);
            let index = len - dbi - 1;
            let (gamma, delta) = &self.looping[index];
            
            // eprintln!("CONTINUE {i}, gamma = {:?}, looping_gamma = {:?}", self.gamma, gamma);
            for (sig, cur) in std::iter::zip(self.gamma.rtypes.iter(), gamma.rtypes.iter())
            {
                self.fun_group.lp.prec(sig, cur);
            }
            for rtype in self.gamma.rtypes.iter()
            {
                self.fun_group.lp.wf(rtype);
            }
            let fresh_gamma = self.fun_group.lp.fresh_gamma(&self.gamma);
            self.gamma = fresh_gamma;
            (delta.clone(), self)
        }
        | Break(i) => {
            // break i = continue i + 1
            let dbi = *i + 1; // De Bruijn Index
            let len = self.looping.len();
            if dbi == len // break
            {
                // eprintln!("BREAK {i}, gamma = {:?}", self.gamma);
                for rtype in self.gamma.rtypes.iter()
                {
                    self.fun_group.lp.wf(rtype);
                }
                let fresh_gamma = self.fun_group.lp.fresh_gamma(&self.gamma);
                self.gamma = fresh_gamma;
                (Resource::Const(0.), self)
            }
            else 
            {
                eprintln!("BREAK AS CONT");
                assert!(dbi < len);
                let index = len - dbi - 1;
                let (gamma, delta) = &self.looping[index];
                for (sig, cur) in std::iter::zip(self.gamma.rtypes.iter(), gamma.rtypes.iter())
                {
                    self.fun_group.lp.prec(sig, cur);
                }
                for rtype in self.gamma.rtypes.iter()
                {
                    self.fun_group.lp.wf(rtype);
                }
                let fresh_gamma = self.fun_group.lp.fresh_gamma(&self.gamma);
                self.gamma = fresh_gamma;
                    
                (delta.clone(), self)
            }
        }
        | _ => unimplemented!("unsupport stmt")
        }
    }
}