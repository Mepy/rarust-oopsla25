use charon_lib::gast::GFunDecl;
use charon_lib::ullbc_ast::Var;
use charon_lib::llbc_ast::Statement;
use charon_lib::types::{Ty, TypeDecl};

use crate::rich_type::RichType;
use crate::functions::FunSig;
use crate::lp::{Resource, RType};

use std::fs::File;
use std::io::{Write, Result};

pub struct Printer
{
    file : File,
    solution : Vec<f64>,
}
impl Printer
{
    pub fn new(file:File) -> Printer
    {
        Printer { file, solution:vec![] }
    }
    pub fn set_solution(self:&mut Printer, solution:Vec<f64>)
    {
        self.solution = solution;
    }
}

fn eval_resource(solution:&Vec<f64>, r:&Resource) -> f64
{
    match r{
        Resource::Var(i) => solution[i.0],
        Resource::Const(f) => *f,
        Resource::Expr(e) => {
            let mut f = 0.;
            for (i, c) in e.var_coefs.iter()
            {
                if i.0 == 0 { f += c; }
                else { f += c * solution[i.0]; }
            }
            f
        },
    }
}
impl Printer 
{
fn print_name(self:&mut Printer, name:&charon_lib::names::Name) -> Result<()>
{
    use charon_lib::names::PathElem::*;
    /* 
    for (i, name) in name.name.iter().enumerate()
    {
        if i!=0 { write!(self.file, "::")? }
        match name
        {
            Ident(name, _) => write!(self.file, "{}", name)?,
            Impl(_) => unimplemented!("name impl"),
        }
    }
    */
    match name.name.last().unwrap()
    {
        Ident(name, _) => write!(self.file, "{}", name),
        Impl(_) => unimplemented!("name impl"),
    }
}

fn print_type(self:&mut Printer, typedecls:&Vec<TypeDecl>, ty:&Ty, rty:&RType) -> Result<()>
{
    use charon_lib::types::{RefKind, TypeId, TypeDeclKind, Field, Variant, AssumedTy};
    match (ty, rty)
    {
    | (Ty::Literal(_literal_ty), RichType::Primitive) => write!(self.file, "Lit"),
    | (Ty::Ref(_region, ty, RefKind::Shared), RichType::Shared(rty))  => {
        write!(self.file, "& ")?; 
        self.print_type(typedecls, &ty, &rty)
    },
    | (Ty::Ref(_region, ty, RefKind::Mut), RichType::Mutable(rtc, rtp)) => {
        write!(self.file, "&mut (")?; 
        self.print_type(typedecls, &ty, &rtc)?;
        write!(self.file, ", ")?;
        self.print_type(typedecls, &ty, &rtp)?;
        write!(self.file, ")")

    },
    | (Ty::Adt(TypeId::Tuple, generic_args), RichType::Tuple(fields, r)) => {
        write!(self.file, "{}, (", eval_resource(&self.solution, r))?;
        for (i, (ty, rty)) in std::iter::zip(generic_args.types.iter(), fields.iter()).enumerate()
        {
            if i!=0 { write!(self.file, ", ")?; }
            self.print_type(typedecls, ty, rty)?;
        }
        write!(self.file, ")")
    }
    | (Ty::Adt(TypeId::Adt(id), _), RichType::SS(tindex)) => {
        let typedecl : &TypeDecl = &typedecls[id.index];
        assert_eq!(id.index, *tindex);
        self.print_name(&typedecl.name)
    }
    | (Ty::Adt(TypeId::Assumed(AssumedTy::Box), generic_args), RichType::BoxOf(rty)) => {
        let ty = &generic_args.types[0];
        let rty : &RType = &rty;
        write!(self.file, "Box(")?;
        self.print_type(typedecls, ty, rty)?;
        write!(self.file, ")")
    }
    | (Ty::Adt(TypeId::Adt(id), _generic_args), RichType::Tuple(rfields, r)) => {
        let typedecl : &TypeDecl = &typedecls[id.index];
        let TypeDeclKind::Struct(fields) = &typedecl.kind else { unreachable!() };
        write!(self.file, "{}, ", eval_resource(&self.solution, r))?;
        self.print_name(&typedecl.name)?;
        write!(self.file, "{{")?;
        for (i, (field, rfield)) in std::iter::zip(fields.iter(), rfields.iter()).enumerate()
        {
            if i!=0 { write!(self.file, ", ")?; }
            let field : &Field = field;
            match &field.name
            {
            | None => { },
            | Some(name) => { write!(self.file, "{}:", name)?; },
            }
            self.print_type(typedecls, &field.ty, rfield)?;
        }
        write!(self.file, "}}")
    }
    | (Ty::Adt(TypeId::Adt(id), _generic_args), RichType::Variant(rvariants)) => {
        let typedecl : &TypeDecl = &typedecls[id.index];
        let TypeDeclKind::Enum(variants) = &typedecl.kind else { unreachable!() };
        self.print_name(&typedecl.name)?; write!(self.file, "[")?;
        for (j, (variant, rvariant)) in std::iter::zip(variants.iter(), rvariants.iter()).enumerate()
        {
            if j!=0 { write!(self.file, ", ")?; }
            let variant : &Variant = variant;
            let (rfields, r) = rvariant;
            write!(self.file, "{}={}(", variant.name, eval_resource(&self.solution, r))?;
            for (i, (field, rfield)) in std::iter::zip(variant.fields.iter(), rfields.iter()).enumerate()
            {
                if i!=0 { write!(self.file, ", ")?; }
                let field : &Field = field;
                match &field.name
                {
                | None => { },
                | Some(name) => { write!(self.file, "{}:", name)?; },
                }
                self.print_type(typedecls, &field.ty, rfield)?;
            }
            write!(self.file, ")")?;
        }
        write!(self.file, "]")
    }
    | (ty, RichType::MR(_, rty))
        => self.print_type(typedecls, ty, rty),
    | _ => unimplemented!("{:?} {:?}", ty, rty),
    }
}

pub fn print_signature(self:&mut Printer, cov:usize, coc:usize, typedecls:&Vec<TypeDecl>, function:&GFunDecl<Statement>, fun_sig:&FunSig) -> Result<()>
{
    self.print_name(&function.name)?;
    writeln!(self.file, " // |constraints| = {coc}"); // |var| = {cov} and 
    write!(self.file, "\t: ")?;
    let Resource::Var(i) = fun_sig.delta else { unreachable!() };
    write!(self.file, "{}", self.solution[i.0])?;
    let Some(body) = &function.body else { unreachable!() };
    for i in 1..=body.arg_count
    {
        write!(self.file, " + ")?;
        let arg : &Var = &body.locals.vector[i];
        
        let Some(name) = &arg.name else { unreachable!() };
        write!(self.file, "{name} : ")?;
        self.print_type(typedecls, &arg.ty, &fun_sig.params[i-1])?;
    }
    write!(self.file, " -> ")?;
    self.print_type(typedecls, &function.signature.output, &fun_sig.ret)?;
    writeln!(self.file, "")
}
}