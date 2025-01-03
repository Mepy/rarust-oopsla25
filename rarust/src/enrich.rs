use std::collections::HashSet;

use crate::rich_type::RichType;
use crate::scc::{make_top_sort, Graph, Node};
use crate::lp::{Resource, RType};
use crate::rich_type::{fold, unfold};

fn type_graph_add_edge(nexts:&mut Vec<usize>, ty:&charon_lib::types::Ty)
{
    use charon_lib::types::Ty::*;
    match ty
    {
    | Literal(_) => (),
    | Adt(tid, gargs) => {
        use charon_lib::types::TypeId::*;
        match tid
        {
        | Adt(tid) => {
            nexts.push(tid.index);
        },
        | Tuple => todo!("tuple need some examples on generic args..."),
        | Assumed(assumed_ty) =>{
            use charon_lib::types::AssumedTy::*;
            match assumed_ty
            {
            | Box => { 
                let ty = &gargs.types[0];
                type_graph_add_edge(nexts, ty);
            }
            | PtrUnique
            | PtrNonNull 
            | Array 
            | Slice
            | Str => unimplemented!("non box assumed types"), 
            }
        }
        }
    },
    | Ref(_region, ty, _ref_kind) => {
        let ty : &charon_lib::types::Ty = &ty;
        type_graph_add_edge(nexts, ty);
    }
    | Never
    | RawPtr(_, _)
    | TypeVar(_)
    | TraitType(_, _, _)
    | Arrow(_, _, _)
        => unimplemented!("no potential-enrich_typedecl support for these types")
    
    }
}
fn make_type_graph(types:&Vec<charon_lib::types::TypeDecl>) -> Graph
{
    let nodes = types.iter().map(|ty|{
        let mut nexts : Vec<usize> = vec![];
        use charon_lib::types::TypeDeclKind::*;
        match &ty.kind
        {
        | Struct(fields) => {
            for field in fields {
                type_graph_add_edge(&mut nexts, &field.ty);
            }
        }
        | Enum(variants) => {
            for variant in variants { 
            for field in &variant.fields {    
                type_graph_add_edge(&mut nexts, &field.ty);
            }
            }
        }
        | Opaque => unimplemented!("not support Opaque types"),
        | Error(_) => unimplemented!("not handled error in type kinds"),
        }
        Node { nexts }
    }).collect::<Vec<Node>>();
    Graph { nodes }
}

fn enrich_typedecl(rtypes:&Vec<RType>, ty:&charon_lib::types::Ty) -> RType
{
    use RichType::*;
    use charon_lib::types::Ty::*;
    match ty
    {
    | Literal(_) => Primitive,
    | Adt(tid, gargs) => {
        use charon_lib::types::TypeId::*;
        match tid
        {
        | Adt(tid) => {
            rtypes[tid.index].clone()
        },
        | Tuple => todo!("tuple need some examples on generic args..."),
        | Assumed(assumed_ty) =>{
            use charon_lib::types::AssumedTy::*;
            match assumed_ty
            {
            | Box => { 
                let ty = &gargs.types[0];
                let rtype = enrich_typedecl(rtypes, ty);
                BoxOf(std::boxed::Box::new(rtype))
            }
            | PtrUnique
            | PtrNonNull 
            | Array 
            | Slice
            | Str => unimplemented!("non box assumed types"), 
            }
        }
        }
    },
    | Ref(_region, ty, ref_kind) => {
        let ty : &charon_lib::types::Ty = &ty;
        match ref_kind
        { 
        | charon_lib::types::RefKind::Shared => {
            let rtype = enrich_typedecl(rtypes, ty);
            Shared(std::boxed::Box::new(rtype))
        }
        | charon_lib::types::RefKind::Mut => {
            let rtype = enrich_typedecl(rtypes, ty);
            Mutable(std::boxed::Box::new(rtype.clone()), std::boxed::Box::new(rtype))
        }
        }
    }
    | Never
    | RawPtr(_, _)
    | TypeVar(_)
    | TraitType(_, _, _)
    | Arrow(_, _, _)
        => unimplemented!("no potential-enrich_typedecl support for these types")
    }
}

fn scan_former(rt:&RType, group:&Vec<usize>, formers:&mut HashSet<usize>)
{
    use RichType::*;
    match rt
    {
    | SS(id) => { formers.insert(*id); },
    | MR(_id, rtype) => { 
        scan_former(&*rtype, group, formers);
    }
    | Undefined | Primitive => (),
    | Tuple(fields, _p) => {
        for rt in fields {
            scan_former(rt, group, formers);
        }
    }
    | Variant(variants) => {
        for (fields, _) in variants {
        for rt in fields {
            scan_former(rt, group, formers);
        }
        }
    }
    | BoxOf(rt) | Shared(rt) => {
        scan_former(rt, group, formers);
    }
    | Mutable(rtc, rtp) => {
        scan_former(rtc, group, formers);
        scan_former(rtp, group, formers);
    }
    }
}

fn former_set(rt:&RType, group:&Vec<usize>) -> HashSet<usize>
{
    let mut formers = HashSet::with_capacity(group.len());
    scan_former(rt, group, &mut formers);
    if let RichType::MR(tindex, _) = rt {
        formers.remove(tindex);
    }
    formers
}
pub fn enrich_typedecls(types:&Vec<charon_lib::types::TypeDecl>) -> Vec<RType>
{
    let type_graph = make_type_graph(types);
    let top_sort = {
        let mut sort = make_top_sort(&type_graph);
        sort.reverse(); // make_type_graph is dual to actual dependency graph
        sort
    };
    /*
    for ty in types 
    {
        eprint!("{:?} ", ty.name);
    }
    eprintln!(""); 
    */
    // eprintln!("{:?}", top_sort);
    let mut rtypes : Vec<RType> = (0..types.len()).map(|i| RichType::SS(i)).collect::<Vec<_>>();

    for group in top_sort {
    let is_mutual = group.len() > 1; // mutual recursive
    for tindex in &group {
        let tindex = *tindex;
        let ty = &types[tindex];
        use charon_lib::types::TypeDeclKind::*;
        let rtype = match &ty.kind
        {
        | Struct(fields) => {
            let rfields = fields.iter().map(|field|{
                enrich_typedecl(&rtypes, &field.ty)
            }).collect::<Vec<_>>();
            RichType::Tuple(rfields, Resource::Const(0.))
        }
        | Enum(variants) => {
            let rvariants = variants.iter().map(|variant|{
                let rfields = variant.fields.iter().map(|field|{
                    enrich_typedecl(&rtypes, &field.ty)
                }).collect::<Vec<_>>();
                (rfields, Resource::Const(0.))
            }).collect::<Vec<_>>();
            RichType::Variant(rvariants)
        }
        | Opaque => unimplemented!("not support Opaque types"),
        | Error(_) => unimplemented!("not handled error in type kinds"),
        };
        if is_mutual { rtypes[tindex] = RichType::MR(tindex, Box::new(rtype)); }
        else { rtypes[tindex] = rtype; }
    }
    if is_mutual {
    // unfold latter with SS(former) as MR(former, rtypes[former])
    // AND fold former with MR(latter, ..) as SS(latter) 
    // formers are from the scanning of latter, todo: using lazy in one-pass for performance(?, I'm not sure)
    for latter in group.iter().rev().skip(1)
    {
        let latter = *latter;
        let former_set = former_set(&rtypes[latter], &group);
        // eprintln!(" latter = {latter}, former_set = {former_set:?}");
        for former in former_set {
            let former_rtype = {
                let RichType::MR(_former, mut rtype) = rtypes[former].clone() else {unreachable!()};
                
                // eprintln!("unfolded former {:?}", rtype);
                fold(&mut rtype, latter);
                // eprintln!("folded former {:?}", rtype);
                rtype
            };
            unfold(&mut rtypes[latter], former, &former_rtype);
        }
    }
    }
    }

    // eprintln!("{:?}", rtypes);
    rtypes
}