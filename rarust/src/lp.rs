/*  linear programming context/layer
    and convert to good_lp representation
*/

use std::fmt;
use std::ops::{Add, Sub};

use crate::rich_type::RichType;
use crate::typ_ctx::Gamma;

pub type GroupIndex = usize;
pub type FunIndex = usize;
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ResourceVarId(pub usize);
impl fmt::Display for ResourceVarId
{
    fn fmt(&self, f:&mut fmt::Formatter) -> fmt::Result
    {
        write!(f, "x{}", self.0)
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct Expression
{
    pub var_coefs : im::OrdMap<ResourceVarId, f64> 
    // { 0 : b, 1 : k_1, ... } <=> \sum_i k_i\alpha_i + b
}
impl fmt::Display for Expression
{
    fn fmt(&self, f:&mut fmt::Formatter) -> fmt::Result
    {
        for (var, coef) in self.var_coefs.iter()
        {
            let coef = *coef;
            if *var == ResourceVarId(0) { write!(f, "{}", coef)? }
            else if coef > 0.0 {
                if coef == 1.0 { write!(f, "+{var}")?; }
                else { write!(f, "+{coef}{var}")?; }
            }
            else if coef < 0.0 {
                if coef == -1.0 { write!(f, "-{var}")?; }
                else { write!(f, "{coef}{var}")?; }
            }
                
        }
        Ok(())
    }
}
/* 
// `new` is never used
impl Expression
{
    fn new() -> Expression
    {
        Expression { var_coefs : im::ordmap!{
            ResourceVarId(0) => 0.
        }}
    }
}
// `add_mul` is never used
impl Expression
{
    fn add_mul(&mut self, coef:f64, var:ResourceVarId)
    {
        match self.var_coefs.get_mut(&var)
        {
        | Some(p) => { *p = *p + coef; }, 
        | None => { self.var_coefs.insert(var, coef); }
        }
    }
}
*/

#[derive(Debug, Clone, PartialEq)]
pub enum Resource
{
    Var(ResourceVarId), // \alpha, assume var_id != 0
    Const(f64),
    Expr(Expression)
}
pub type RType = RichType<Resource>;

impl fmt::Display for Resource
{
    fn fmt(&self, f:&mut fmt::Formatter) -> fmt::Result
    {
        use Resource::*;
        match self
        {
        | Var(id) => write!(f, "{}", id),
        | Const(cost) => write!(f, "{}", cost),
        | Expr(expr) => write!(f, "{}", expr),
        }
    }
}

impl Add for Resource
{
    type Output = Resource;

    fn add(self, rhs: Self) -> Self::Output 
    {
        use Resource::*;
        match (self, rhs)
        {
        | (Var(x1), Var(x2)) =>
            if x1 == x2 
            {
                Expr(Expression { var_coefs : im::ordmap!{
                    ResourceVarId(0) => 0.0,
                    x1 => 2.0
                }})
            }
            else
            {
                Expr(Expression { var_coefs : im::ordmap!{
                    ResourceVarId(0) => 0.0,
                    x1 => 1.0,
                    x2 => 1.0
                }})
            }
        | (Const(b1), Const(b2)) => Const(b1+b2),
        | (Expr(Expression{var_coefs:vc1}), Expr(Expression { var_coefs:vc2 })) =>
            Expr(Expression { var_coefs : vc1.union_with(vc2, |c1, c2| c1+c2) }),
        | (Var(x), Const(b)) | (Const(b), Var(x)) =>
            Expr(Expression { var_coefs : im::ordmap!{
                ResourceVarId(0) => b,
                x => 1.0
            }}),
        | (Var(x), Expr(Expression { mut var_coefs })) | (Expr(Expression { mut var_coefs }), Var(x)) => {
            match var_coefs.get_mut(&x)
            {
            | Some(p) => { *p = *p + 1.0; }, 
            | None => { var_coefs.insert(x, 1.0); }
            }
            Expr(Expression{var_coefs})
        },
        | (Const(b), Expr(Expression { mut var_coefs })) | (Expr(Expression { mut var_coefs }), Const(b)) => {
            match var_coefs.get_mut(&ResourceVarId(0))
            {
            | Some(p) => { *p = *p + b; }, 
            | None => { var_coefs.insert(ResourceVarId(0), b); }
            }
            Expr(Expression{var_coefs})
        },
        }
    }
}
impl Sub for Resource
{
    type Output = Resource;

    fn sub(self, rhs: Self) -> Self::Output 
    {
        use Resource::*;
        match (self, rhs)
        {
        | (Var(x1), Var(x2)) =>
            if x1 == x2 
            {
                Expr(Expression { var_coefs : im::ordmap!{
                    ResourceVarId(0) => 0.0
                }})
            }
            else
            {
                Expr(Expression { var_coefs : im::ordmap!{
                    ResourceVarId(0) => 0.0,
                    x1 => 1.0,
                    x2 => -1.0
                }})
            }
        | (Const(b1), Const(b2)) => Const(b1-b2),
        | (Expr(Expression{var_coefs:vc1}), Expr(Expression { var_coefs:vc2 })) => {
            let neg_vc2 = im::OrdMap::from(
                vc2.into_iter()
                .map(|(k, v)|{ (k, -v)}).collect::<Vec<_>>()
            );
            Expr(Expression { var_coefs : vc1.union_with(neg_vc2, |c1, c2| c1+c2) })
        },
        | (Var(x), Const(b)) =>
            Expr(Expression { var_coefs : im::ordmap!{
                ResourceVarId(0) => -b,
                x => 1.0
            }}),
        | (Const(b), Var(x)) =>
            Expr(Expression { var_coefs : im::ordmap!{
                ResourceVarId(0) => b,
                x => -1.0
            }}),
        | (Var(x), Expr(Expression { var_coefs })) => {
            let mut var_coefs : im::OrdMap<ResourceVarId, f64> = im::OrdMap::from(
                var_coefs.into_iter()
                .map(|(k, v)|{ (k, -v) }).collect::<Vec<_>>()
            );
            match var_coefs.get_mut(&x)
            {
            | Some(p) => { *p = *p + 1.0; }, 
            | None => { var_coefs.insert(x, 1.0); }
            }
            Expr(Expression{var_coefs})
        },
        | (Expr(Expression { mut var_coefs }), Var(x)) => {
            match var_coefs.get_mut(&x)
            {
            | Some(p) => { *p = *p - 1.0; }, 
            | None => { var_coefs.insert(x, -1.0); }
            }
            Expr(Expression{var_coefs})
        },
        | (Const(b), Expr(Expression { var_coefs })) => {
            let mut var_coefs : im::OrdMap<ResourceVarId, f64> = im::OrdMap::from(
                var_coefs.into_iter()
                .map(|(k, v)|{ (k, -v) }).collect::<Vec<_>>()
            );
            match var_coefs.get_mut(&ResourceVarId(0))
            {
            | Some(p) => { *p = *p + b; }, 
            | None => { var_coefs.insert(ResourceVarId(0), b); }
            }
            Expr(Expression{var_coefs})
        }
        | (Expr(Expression { mut var_coefs }), Const(b)) => {
            match var_coefs.get_mut(&ResourceVarId(0))
            {
            | Some(p) => { *p = *p - b; }, 
            | None => { var_coefs.insert(ResourceVarId(0), -b); }
            }
            Expr(Expression{var_coefs})
        },
        }
    }
}


#[derive(Debug, Clone)]
pub enum Constraint
{
    EqZero(Expression),  // expr == 0
    GeqZero(Expression), // expr >= 0
    LeqZero(Expression), // expr <= 0
}
impl fmt::Display for Constraint
{
    fn fmt(&self, f:&mut fmt::Formatter) -> fmt::Result
    {
        use Constraint::*;
        match self
        {
        | EqZero(expr) => write!(f, "{expr}=0"),
        | GeqZero(expr) => write!(f, "{expr}>=0"),
        | LeqZero(expr) => write!(f, "{expr}<=0"),
        }
    }
}

#[macro_export]
macro_rules! get_expr {
    ($e:expr) => {
        match $e {
            Resource::Expr(e) => e,
            _ => unreachable!(),
        }
    };
}

/** copy from good_lp::constraint! */
#[macro_export]
macro_rules! constraint {
    ([$($left:tt)*] <= $($right:tt)*) => {
        crate::lp::Constraint::LeqZero(get_expr!(($($left)*) - ($($right)*)))
    };
    ([$($left:tt)*] >= $($right:tt)*) => {
        crate::lp::Constraint::GeqZero(get_expr!(($($left)*) - ($($right)*)))
    };
    ([$($left:tt)*] == $($right:tt)*) => {
        crate::lp::Constraint::EqZero(get_expr!(($($left)*) - ($($right)*)))
    };
    // Stop condition: all token have been processed
    ([$($left:tt)*]) => {
        $($left:tt)*
    };
    // The next token is not a special one
    ([$($left:tt)*] $next:tt $($right:tt)*) => {
        constraint!([$($left)* $next] $($right)*)
    };
    // Initial rule: start the recursive calls
    ($($all:tt)*) => {
        constraint!([] $($all)*)
    };
}
 
#[derive(Debug, Clone)]
/// \alpha \in symbolics -> list(\alpha) is the resource of a symbolic list
pub struct Lp 
{
    pub var_size : ResourceVarId,

    /// we do NOT add alpha>=0 for function execution;
    /// we add them only when solving linear programme
    pub constraints : im::Vector<Constraint>,

    pub symbolics : im::HashSet<ResourceVarId>, 
}
impl fmt::Display for Lp
{
    fn fmt(&self, f:&mut fmt::Formatter) -> fmt::Result
    {
        write!(f, "constraints:[\n")?;
        for constraint in self.constraints.iter()
        {
            write!(f, "{constraint},\n")?;
        }
        write!(f, "]\n")
    }
}
impl Lp
{
    pub fn fresh(&mut self) -> Resource
    {
        self.var_size.0 += 1;
        Resource::Var(self.var_size)
    }
    /* 
    /// see [`Lp`].symbolics
    pub fn fresh_symbol(&mut self) -> Resource
    {
        self.var_size.0 += 1;
        self.symbolics.insert(self.var_size);
        Resource::Var(self.var_size)
    }
    */
    /** the prophecy */
    pub fn fresh_rtype(&mut self, rtype:&RichType<Resource>) -> RichType<Resource>
    {
        use RichType::*;
        match rtype
        {
        | Undefined => Undefined,
        | Primitive => Primitive,
        | Tuple(rfields, _r) => {
            let rfieldsp = rfields.iter()
                .map(|rtype|{ self.fresh_rtype(rtype) })
                .collect::<Vec<_>>();
            let rp = self.fresh();
            Tuple(rfieldsp, rp)
        },
        | Variant(rvariants) => {
            let rvariantsp = rvariants.iter()
                .map(|(rfields, _r)|{
                    let rfieldsp = rfields.iter()
                    .map(|rtype|{ self.fresh_rtype(rtype) })
                    .collect::<Vec<_>>();
                    let rp = self.fresh();
                    (rfieldsp, rp)
                }).collect::<Vec<_>>();
            Variant(rvariantsp)
        },
        | SS(tindex) => SS(*tindex),
        | MR(tindex, rt) => MR(*tindex, Box::new(self.fresh_rtype(&rt))),
        | BoxOf(rt) => BoxOf(Box::new(self.fresh_rtype(&rt))),
        | Shared(rt) => Shared(Box::new(self.fresh_rtype(&rt))),
        | Mutable(rtc, rtp) 
            => Mutable(Box::new(self.fresh_rtype(&rtc)), Box::new(self.fresh_rtype(&rtp))),
        }
    }
    pub fn fresh_gamma(&mut self, gamma:&Gamma) -> Gamma 
    {
        let Gamma{ rtypes } = gamma;
        let rtypes = rtypes.iter().map(|rtype|{ self.fresh_rtype(rtype) }).collect::<im::Vector<_>>();
        Gamma { rtypes }
    }
    pub fn add(&mut self, constraint:Constraint)
    {
        self.constraints.push_back(constraint);
    }
    pub fn min(&mut self, alpha1:Resource, alpha2:Resource) -> Resource
    {
        use Resource::*;
        match (alpha1, alpha2)
        {
        // if x1 == x2 => Var(x1) works well for reducing the count of variables
        | (Var(x1), Var(x2)) if x1 == x2 => Var(x1),
        | (alpha1, alpha2) => { 
            let alpha = self.fresh();
            self.add(constraint!(alpha.clone() <= alpha1));
            self.add(constraint!(alpha.clone() <= alpha2));
            alpha
        }
        }
    }
    pub fn mins(&mut self, alphas:Vec<Resource>) -> Resource
    {
        
        if alphas.len() == 1 { alphas[0].clone() }
        else 
        {
            let alpha = self.fresh();
            for alphai in alphas
            {
                self.add(constraint!(alpha.clone() <= alphai));
            }
            alpha
        }
    }
    pub fn max(&mut self, alpha1:Resource, alpha2:Resource) -> Resource
    {
        use Resource::*;
        match (alpha1, alpha2)
        {
        | (Var(x1), Var(x2)) if x1 == x2 => Var(x1),
        | (alpha1, alpha2) => { 
            let alpha = self.fresh();
            self.add(constraint!(alpha.clone() >= alpha1));
            self.add(constraint!(alpha.clone() >= alpha2));
            alpha
        }
        }
    }
    pub fn maxs(&mut self, alphas:Vec<Resource>) -> Resource
    {
        if alphas.len() == 1 { alphas[0].clone() }
        else 
        {
            let alpha = self.fresh();
            for alphai in alphas
            {
                self.add(constraint!(alpha.clone() >= alphai));
            }
            alpha
        }

    }
    pub fn split(&mut self, alpha:Resource) -> (Resource, Resource)
    {
        let alpha1 = self.fresh();
        let alpha2 = self.fresh();
        self.add(constraint!(alpha1.clone() + alpha2.clone() == alpha));
        (alpha1, alpha2)
    }
}

pub struct Convertor
{
    pub variables : Vec<good_lp::Variable>,
}
impl Convertor
{
    pub fn expr(&self, expr:&Expression) -> good_lp::Expression
    {
        let mut obj : good_lp::Expression = expr.var_coefs[&ResourceVarId(0)].into();
        for (var, coef) in expr.var_coefs.iter().skip(1)
        {
            obj.add_mul(*coef, self.variables[var.0]);
        }
        obj
    }
    pub fn resource(&self, resource:&Resource) -> good_lp::Expression
    {
        match resource
        {
        | Resource::Var(var) => self.variables[var.0].into(),
        | Resource::Const(c) => (*c).into(),
        | Resource::Expr(expr) => self.expr(expr),
        }
    }
    pub fn constraint(&self, constraint:&Constraint) -> good_lp::Constraint
    {
        match constraint
        {
            Constraint::EqZero(expr) => self.expr(expr).eq(0),
            Constraint::GeqZero(expr) => self.expr(expr).geq(0),
            Constraint::LeqZero(expr) => self.expr(expr).leq(0),
        }
    }
}

// lifter for lp instantiation
pub struct Lifter
{
    pub offset : usize,
}
impl Lifter
{
    pub fn expr(&self, expr:&Expression) -> Expression
    {
        let mut var_coefs = expr.var_coefs.iter().skip(1)
        .map(|(var, coef)|{ 
            (ResourceVarId(var.0+self.offset), *coef) 
        }).collect::<im::OrdMap<_, _>>();
        match expr.var_coefs.get(&ResourceVarId(0))
        {
        | None => (),
        | Some(c) => { var_coefs.insert(ResourceVarId(0), *c); }
        }
        Expression { var_coefs }
    }
    pub fn resource(&self, resource:&Resource) -> Resource
    {
        use Resource::*;
        match resource
        {
        | Var(var) => Var(ResourceVarId(var.0+self.offset)),
        | Const(c) => Const(*c),
        | Expr(expr) => Expr(self.expr(expr)),
        }
    }
    pub fn rtype(&self, rtype:&RType) -> RType
    {
        // unsafe { eprintln!("{} : {:?}", crate::llbc::TEST_ITER, rtype); crate::llbc::TEST_ITER += 1; }
        use RichType::*;
        match rtype 
        {
        | Undefined => Undefined,
        | Primitive => Primitive,
        | Tuple(rfields, r) => {
            let rfields_lift = rfields.iter().map(|rtype|{ self.rtype(rtype) }).collect::<Vec<_>>();
            let r_lift = self.resource(r);
            Tuple(rfields_lift, r_lift)
        },
        | Variant(rvariants) => {
            let rvariants_lift = rvariants.iter()
            .map(|(rfields, r)|{
                let rfields_lift = rfields.iter().map(|rtype|{ self.rtype(rtype) }).collect::<Vec<_>>();
                let r_lift = self.resource(r);
                (rfields_lift, r_lift)
            }).collect::<Vec<_>>();
            Variant(rvariants_lift)
        },
        | SS(tindex) => SS(*tindex),
        | MR(tindex, rtype) => MR(*tindex, Box::new(self.rtype(rtype))),
        | BoxOf(rtype) => BoxOf(Box::new(self.rtype(rtype))),
        | Shared(rtype) => Shared(Box::new(self.rtype(rtype))),
        | Mutable(rtc, rtp) => Mutable(Box::new(self.rtype(&rtc)), Box::new(self.rtype(rtp))),
        }
    }
    pub fn constraint(&self, constraint:&Constraint) -> Constraint
    {
        use Constraint::*;
        match constraint
        {
        | EqZero(expr) => EqZero(self.expr(expr)),
        | GeqZero(expr) => GeqZero(self.expr(expr)),
        | LeqZero(expr) => LeqZero(self.expr(expr)),
        }
    }
}

