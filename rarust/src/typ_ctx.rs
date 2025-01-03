use charon_lib::gast::{FieldProjKind, Place};

use crate::{lp::RType, rich_type::{extract, fold, unfold, RichType}};


#[derive(Debug, Clone)]
pub struct Gamma
{
    pub rtypes : im::Vector<RType>
}

impl Gamma
{
    pub fn read(&self, place:&Place) -> RType
    {
        let Place{var_id, projection} = place;
        let i = var_id.index;
        let mut rtype= self.rtypes[i].clone();
        for proj in projection
        {
            use charon_lib::ullbc_ast::ProjectionElem::*;
            use RichType::*;
            match proj
            {
            | Deref => match rtype {
                | Shared(rt)
                | Mutable(rt, _) => { rtype = *rt; }
                | _ /* Primitive | Tuple(_, _) | Variant(_) | SS | BoxOf(_) */
                    => unreachable!("Deref {:?}", rtype),
            }
            | DerefBox => match rtype {
                | BoxOf(rt) => { rtype = *rt; }
                | _ => unreachable!(), 
            }
            | Field(FieldProjKind::Tuple(_arity), field_id) =>
            {
                let Tuple(rfields, _) = &rtype else { unreachable!() };
                rtype = rfields[field_id.index].clone();
            }
            | Field(FieldProjKind::Adt(adt_id, Some(variant_id)), field_id) => {
                if let MR(outer,  rty) = &rtype {
                // mutual recursive
                let outer = *outer;
                let rty : RType = *rty.clone();
                let Variant(rvariants) = &rty else { unreachable!() };
                let (rfields, _alpha) = &rvariants[variant_id.index];
                let rt = &rfields[field_id.index];
                
                // eprintln!("{rtype:?}");
                // eprintln!("{rt:?}");
                match rt
                {
                | BoxOf(rt0) => {
                    let rt0 : &RType = rt0;
                    match rt0
                    {
                    | MR(inner, rt)
                        => { 
                            let inner = *inner;
                            let mut inner_rtype : RType = *rt.clone();
                            let mut outer_rtype = rty.clone();
                            fold(&mut outer_rtype, inner);
                            unfold(&mut inner_rtype, outer, &outer_rtype);
                            rtype = BoxOf(Box::new(MR(inner, Box::new(inner_rtype)))); 
                            // eprintln!("rtype update {rtype:?}");
                        },
                        // additive shift
                    | _ => { rtype = rt.clone(); },
                    }
                },
                | MR(inner, rt) => { 
                    let inner = *inner;
                    let mut inner_rtype : RType = *rt.clone();
                    let mut outer_rtype = rty.clone();
                    fold(&mut outer_rtype, inner);
                    unfold(&mut inner_rtype, outer, &outer_rtype);
                    rtype = MR(inner, Box::new(inner_rtype)); 
                },
                | _ => { rtype = rt.clone(); },
                }
                }
                else {
                let Variant(rvariants) = &rtype else { unreachable!() };
                let (rfields, _alpha) = &rvariants[variant_id.index];
                let rt = &rfields[field_id.index];
                match rt
                {
                | BoxOf(rt0) => {
                    let rt0 : &RType = rt0;
                    match rt0
                    {
                    | SS(tindex) if *tindex == adt_id.index 
                        => { rtype = BoxOf(std::boxed::Box::new(rtype)); },
                        // additive shift
                    | _ => { rtype = rt.clone(); },
                    }
                },
                | _ => { rtype = rt.clone(); },
                }
                }
            }
            | Field(FieldProjKind::Adt(adt_id, None), field_id) => { 
                // structs are adts with only one variant
                if let MR(outer,  rty) = &rtype {
                // mutual recursive
                let outer = *outer;
                let rty : RType = *rty.clone();
                let Tuple(rfields, _alpha) = &rty else { unreachable!() };
                let rt = &rfields[field_id.index];
                
                // eprintln!("{rtype:?}");
                // eprintln!("{rt:?}");
                match rt
                {
                | BoxOf(rt0) => {
                    let rt0 : &RType = rt0;
                    match rt0
                    {
                    | MR(inner, rt)
                        => { 
                            let inner = *inner;
                            let mut inner_rtype : RType = *rt.clone();
                            let mut outer_rtype = rty.clone();
                            fold(&mut outer_rtype, inner);
                            unfold(&mut inner_rtype, outer, &outer_rtype);
                            rtype = BoxOf(Box::new(MR(inner, Box::new(inner_rtype)))); 
                            // eprintln!("rtype update {rtype:?}");
                        },
                        // additive shift
                    | _ => { rtype = rt.clone(); },
                    }
                },
                | MR(inner, rt) => { 
                    let inner = *inner;
                    let mut inner_rtype : RType = *rt.clone();
                    let mut outer_rtype = rty.clone();
                    fold(&mut outer_rtype, inner);
                    unfold(&mut inner_rtype, outer, &outer_rtype);
                    rtype = MR(inner, Box::new(inner_rtype)); 
                },
                | _ => { 
                    rtype = rt.clone(); },
                }
                }
                else {
                let Tuple(rfields, _alpha) = &rtype else { unreachable!() };
                let rt = &rfields[field_id.index];
                match rt
                {
                | BoxOf(rt0) => {
                    let rt0 : &RType = rt0;
                    match rt0
                    {
                    | SS(tindex) if *tindex == adt_id.index 
                        => { rtype = BoxOf(std::boxed::Box::new(rtype)); },
                        // additive shift
                    | _ => { rtype = rt.clone(); },
                    }
                },
                | _ => { rtype = rt.clone(); },
                }
                }
            }
            | DerefRawPtr => todo!(),
            | Field(_, _) => todo!(),
            | Index(_, _) => todo!(),
            }
        }
        rtype
    }
    
    pub fn write(&mut self, place:&Place, rtype:RType)
    {
        let Place{var_id, projection} = place;
        let i = var_id.index;
        
        let mut rtype = rtype;
        let mut p = &mut self.rtypes[i];
        for proj in projection
        {
            use charon_lib::ullbc_ast::ProjectionElem::*;
            use RichType::*;
            match proj
            {
            | Deref => match p {
                | Shared(rt)
                | Mutable(rt, _) => { p = &mut *rt; }
                | _ /* Primitive | Tuple(_, _) | Variant(_) | SS | BoxOf(_) */
                    => unreachable!(),
            },
            | DerefBox => match p {
                | BoxOf(rt) => { p = &mut *rt },
                | _ => unreachable!(),
            },
            | Field(FieldProjKind::Tuple(_arity), field_id) =>
            {
                let Tuple(rfields, _) = p else { unreachable!() };
                p = &mut rfields[field_id.index];
            },
            | Field(FieldProjKind::Adt(adt_id, Some(variant_id)), field_id) => {
                if let MR(outer,  rty) = &p {
                // mutual recursive
                // eprintln!("P {p:?}");
                let outer = *outer;
                let rty : RType = *rty.clone();
                let Variant(rvariants) = &rty else { unreachable!() };
                let (rfields, _alpha) = &rvariants[variant_id.index];
                let rt = &rfields[field_id.index];

                // eprintln!("XXXX {rt:?}");

                // eprintln!("YYYY rtype {rtype:?}");
                
                match rt
                {
                | BoxOf(rt0) => {
                    let rt0 : &RType = rt0;
                    match rt0
                    {
                    | MR(inner, _rt) => { 
                        let inner = *inner;
                        let _outer_rtype = rty.clone();
                        if let Some(mut new_rtype) = extract(&rtype, outer)
                        {
                            let MR(_outer, inner_rtype) = rtype else { unreachable!() };
                            let mut inner_rtype : RType = *inner_rtype;
                            fold(&mut inner_rtype, outer);
                            unfold(&mut new_rtype, inner, &inner_rtype);
                            rtype = MR(outer, Box::new(new_rtype)); 
                            // eprintln!("rtype {p:?} := update {rtype:?}");
                        }
                        else
                        {
                            let MR(_, rty) = p else { unreachable!(); };
                            let Tuple(rfields, _alpha) = &mut **rty else { unreachable!(); };
                            p = &mut rfields[field_id.index];  
                        }
                    }, // additive shift
                    | _ => { 
                        let MR(_, rty) = p else { unreachable!(); };
                        let Variant(rvariants) = &mut **rty else { unreachable!() };
                        let (rfields, _alpha) = &mut rvariants[variant_id.index];
                        p = &mut rfields[field_id.index];
                    },
                    }
                },
                | MR(inner, _rt) => { 
                    let inner = *inner;
                    let _outer_rtype = rty.clone();
                    if let Some(mut new_rtype) = extract(&rtype, outer)
                    {
                        let MR(_outer, inner_rtype) = rtype else { unreachable!() };
                        let mut inner_rtype : RType = *inner_rtype;
                        fold(&mut inner_rtype, outer);
                        unfold(&mut new_rtype, inner, &inner_rtype);
                        rtype = MR(outer, Box::new(new_rtype)); 
                        // eprintln!("rtype {p:?} := update {rtype:?}");
                    }
                    else
                    {
                        let MR(_, rty) = p else { unreachable!(); };
                        let Variant(rvariants) = &mut **rty else { unreachable!() };
                        let (rfields, _alpha) = &mut rvariants[variant_id.index];
                        p = &mut rfields[field_id.index];
                    }
                },
                | _ => { 
                    let MR(_, rty) = p else { unreachable!(); };
                    let Variant(rvariants) = &mut **rty else { unreachable!() };
                    let (rfields, _alpha) = &mut rvariants[variant_id.index];
                    p = &mut rfields[field_id.index];
                },
                }
                }
                else{
                let Variant(rvariants) = &p else { unreachable!() };
                let (rfields, _alpha) = &rvariants[variant_id.index];
                // let rt = &mut rfields[field_id.index];
                
                match &rfields[field_id.index]
                {
                | BoxOf(rt0) => {
                    let rt0 : &RType = &rt0;
                    match rt0
                    {
                    | SS(tindex) if *tindex == adt_id.index =>{
                        // reverse of additive shift
                        let BoxOf(rt1) = rtype else { unreachable!() };
                        rtype = *rt1;
                        //  Box($) := Box(rt1) iff $ := rt1
                    }
                    | _ => { 
                        let Variant(rvariants) = p else { unreachable!(); };
                        let (rfields, _alpha) = &mut rvariants[variant_id.index];
                        p = &mut rfields[field_id.index]; 
                    },
                    }
                    
                },
                | _ => { 
                    let Variant(rvariants) = p else { unreachable!(); };
                    let (rfields, _alpha) = &mut rvariants[variant_id.index];
                    p = &mut rfields[field_id.index];  
                },
                }
                }
            }

            | Field(FieldProjKind::Adt(adt_id, None), field_id) => {
                if let MR(outer,  rty) = &p {
                // mutual recursive
                // eprintln!("P {p:?}");
                let outer = *outer;
                let rty : RType = *rty.clone();
                let Tuple(rfields, _alpha) = &rty else { unreachable!() };
                let rt = &rfields[field_id.index];

                // eprintln!("XXXX {rt:?}");

                // eprintln!("YYYY rtype {rtype:?}");
                
                match rt
                {
                | BoxOf(rt0) => {
                    let rt0 : &RType = rt0;
                    match rt0
                    {
                    | MR(inner, _rt) => { 
                        let inner = *inner;
                        let _outer_rtype = rty.clone();
                        if let Some(mut new_rtype) = extract(&rtype, outer)
                        {
                            let MR(_outer, inner_rtype) = rtype else { unreachable!() };
                            let mut inner_rtype : RType = *inner_rtype;
                            fold(&mut inner_rtype, outer);
                            unfold(&mut new_rtype, inner, &inner_rtype);
                            rtype = MR(outer, Box::new(new_rtype)); 
                            // eprintln!("rtype {p:?} := update {rtype:?}");
                        }
                        else
                        {
                            let MR(_, rty) = p else { unreachable!(); };
                            let Tuple(rfields, _alpha) = &mut **rty else { unreachable!(); };
                            p = &mut rfields[field_id.index];  
                        }
                    }, // additive shift
                    | _ => { 
                        let MR(_, rty) = p else { unreachable!(); };
                        let Tuple(rfields, _alpha) = &mut **rty else { unreachable!(); };
                        p = &mut rfields[field_id.index];  
                    },
                    }
                },
                | MR(inner, _rt) => { 
                    let inner = *inner;
                    let _outer_rtype = rty.clone();
                    if let Some(mut new_rtype) = extract(&rtype, outer)
                    {
                        let MR(_outer, inner_rtype) = rtype else { unreachable!() };
                        let mut inner_rtype : RType = *inner_rtype;
                        fold(&mut inner_rtype, outer);
                        unfold(&mut new_rtype, inner, &inner_rtype);
                        rtype = MR(outer, Box::new(new_rtype)); 
                        // eprintln!("rtype {p:?} := update {rtype:?}");
                    }
                    else
                    {
                        let MR(_, rty) = p else { unreachable!(); };
                        let Tuple(rfields, _alpha) = &mut **rty else { unreachable!(); };
                        p = &mut rfields[field_id.index];  
                    }
                },
                | _ => { 
                    let MR(_, rty) = p else { unreachable!(); };
                    let Tuple(rfields, _alpha) = &mut **rty else { unreachable!(); };
                    p = &mut rfields[field_id.index];  
                },
                }
                }
                else {
                let Tuple(rfields, _alpha) = &p else { unreachable!() };
                match &rfields[field_id.index]
                {
                | BoxOf(rt0) => {
                    let rt0 : &RType = &rt0;
                    match rt0
                    {
                    | SS(tindex) if *tindex == adt_id.index =>{
                        // reverse of additive shift
                        let BoxOf(rt1) = rtype else { unreachable!() };
                        rtype = *rt1;
                        //  Box($) := Box(rt1) iff $ := rt1
                    }
                    | _ => { 
                        let Tuple(rfields, _alpha) = p else { unreachable!(); };
                        p = &mut rfields[field_id.index]; 
                    },
                    }
                    
                },
                | _ => { 
                    let Tuple(rfields, _alpha) = p else { unreachable!(); };
                    p = &mut rfields[field_id.index];  
                },
                }
                }
            }
            | DerefRawPtr => todo!(),
            | Field(_, _) => todo!(), 
            | Index(_, _) => todo!(),
            }
        }
        *p = rtype;
    }
 
}