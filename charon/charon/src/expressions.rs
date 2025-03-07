//! Implements expressions: paths, operands, rvalues, lvalues

pub use crate::expressions_utils::*;
use crate::gast::{FunDeclId, TraitItemName};
use crate::types::*;
pub use crate::values::VarId;
use crate::values::*;
use macros::{EnumAsGetters, EnumIsA, EnumToGetters, VariantIndexArity, VariantName};
use serde::{Serialize, Deserialize};
use std::vec::Vec;

#[derive(Debug, PartialEq, Eq, Clone, Serialize, Deserialize)]
pub struct Place {
    // TODO: update to transform to a recursive type
    pub var_id: VarId::Id,
    pub projection: Projection,
}

pub type Projection = Vec<ProjectionElem>;

/// Note that we don't have the equivalent of "downcasts".
/// Downcasts are actually necessary, for instance when initializing enumeration
/// values: the value is initially `Bottom`, and we need a way of knowing the
/// variant.
/// For example:
/// `((_0 as Right).0: T2) = move _1;`
/// In MIR, downcasts always happen before field projections: in our internal
/// language, we thus merge downcasts and field projections.
#[derive(
    Debug, PartialEq, Eq, Clone, EnumIsA, EnumAsGetters, EnumToGetters, VariantName, Serialize, Deserialize,
)]
pub enum ProjectionElem {
    /// Dereference a shared/mutable reference.
    Deref,
    /// Dereference a boxed value.
    /// Note that this doesn't exist in MIR where `Deref` is used both for the
    /// mutable and shared references *and* the boxed values. As semantically we
    /// don't handle those two cases the same way at all, we disambiguate them
    /// during the translation.
    /// In rust, this comes from the `*` operator applied on boxes.
    DerefBox,
    /// Dereference a raw pointer. See the comments for [crate::types::Ty::RawPtr].
    /// TODO: remove those (we would also need: `DerefPtrUnique`, `DerefPtrNonNull`, etc.)
    /// and only keep a single `Deref` variant?
    /// Or if we keep them, change to: `Deref(DerefKind)`?
    DerefRawPtr,
    /// Projection from ADTs (variants, structures).
    /// We allow projections to be used as left-values and right-values.
    /// We should never have projections to fields of symbolic variants (they
    /// should have been expanded before through a match).
    /// Note that in MIR, field projections don't contain any type information
    /// (adt identifier, variant id, etc.). This information can be valuable
    /// (for pretty printing for instance). We retrieve it through
    /// type-checking.
    Field(FieldProjKind, FieldId::Id),
    /// MIR imposes that the argument to an index projection be a local variable, meaning
    /// that even constant indices into arrays are let-bound as separate variables.
    /// We also keep the type of the array/slice that we index for convenience purposes
    /// (this is not necessary).
    /// We **eliminate** this variant in a micro-pass.
    Index(VarId::Id, Ty),
}

#[derive(Debug, PartialEq, Eq, Copy, Clone, EnumIsA, EnumAsGetters, Serialize, Deserialize)]
pub enum FieldProjKind {
    #[serde(rename = "ProjAdt")]
    Adt(TypeDeclId::Id, Option<VariantId::Id>),
    /// If we project from a tuple, the projection kind gives the arity of the tuple.
    #[serde(rename = "ProjTuple")]
    Tuple(usize),
    #[serde(rename = "ProjClosureState")]
    /// Access to a field in a closure state.
    /// We eliminate this in a micro-pass ([crate::update_closure_signatures]).
    ClosureState,
}

#[derive(Debug, PartialEq, Eq, Copy, Clone, EnumIsA, EnumAsGetters, Serialize, Deserialize)]
pub enum BorrowKind {
    Shared,
    Mut,
    /// See <https://doc.rust-lang.org/beta/nightly-rustc/rustc_middle/mir/enum.BorrowKind.html#variant.Mut>
    /// and <https://rustc-dev-guide.rust-lang.org/borrow_check/two_phase_borrows.html>
    TwoPhaseMut,
    /// See <https://doc.rust-lang.org/beta/nightly-rustc/rustc_middle/mir/enum.BorrowKind.html#variant.Shallow>.
    ///
    /// Those are typically introduced when using guards in matches, to make
    /// sure guards don't change the variant of an enumeration value while me
    /// match over it.
    Shallow,
}

/// Unary operation
#[derive(Debug, PartialEq, Eq, Clone, EnumIsA, VariantName, Serialize, Deserialize)]
pub enum UnOp {
    Not,
    /// This can overflow. In practice, rust introduces an assert before
    /// (in debug mode) to check that it is not equal to the minimum integer
    /// value (for the proper type).
    Neg,
    /// Casts are rvalues in MIR, but we treat them as unops.
    Cast(CastKind),
    /// Coercion from array (i.e., [T; N]) to slice.
    ///
    /// **Remark:** We introduce this unop when translating from MIR, **then transform**
    /// it to a function call in a micro pass. The type and the scalar value are not
    /// *necessary* as we can retrieve them from the context, but storing them here is
    /// very useful. The [RefKind] argument states whethere we operate on a mutable
    /// or a shared borrow to an array.
    ArrayToSlice(RefKind, Ty, ConstGeneric),
}

/// For all the variants: the first type gives the source type, the second one gives
/// the destination type.
#[derive(Debug, PartialEq, Eq, Clone, EnumIsA, VariantName, Serialize, Deserialize)]
pub enum CastKind {
    /// Conversion between types in {Integer, Bool}
    /// Remark: for now we don't support conversions with Char.
    Scalar(LiteralTy, LiteralTy),
    FnPtr(Ty, Ty),
}

/// Binary operations.
#[derive(Debug, PartialEq, Eq, Copy, Clone, EnumIsA, VariantName, Serialize, Deserialize)]
pub enum BinOp {
    BitXor,
    BitAnd,
    BitOr,
    Eq,
    Lt,
    Le,
    Ne,
    Ge,
    Gt,
    /// Can fail if the divisor is 0.
    Div,
    /// Can fail if the divisor is 0.
    Rem,
    /// Can overflow
    Add,
    /// Can overflow
    Sub,
    /// Can overflow
    Mul,
    /// Can fail if the shift is too big
    Shl,
    /// Can fail if the shift is too big
    Shr,
    // No Offset binary operation: this is an operation on raw pointers
}

#[derive(
    Debug, PartialEq, Eq, Clone, EnumIsA, EnumToGetters, EnumAsGetters, VariantName, Serialize, Deserialize
)]
pub enum Operand {
    Copy(Place),
    Move(Place),
    /// Constant value (including constant and static variables)
    Const(ConstantExpr),
}

/// A function identifier. See [crate::ullbc_ast::Terminator]
#[derive(Debug, Clone, PartialEq, Eq, EnumIsA, EnumAsGetters, VariantName, Serialize, Deserialize)]
pub enum FunId {
    /// A "regular" function (function local to the crate, external function
    /// not treated as a primitive one).
    Regular(FunDeclId::Id),
    /// A primitive function, coming from a standard library (for instance:
    /// `alloc::boxed::Box::new`).
    /// TODO: rename to "Primitive"
    Assumed(AssumedFunId),
}

/// An assumed function identifier, identifying a function coming from a
/// standard library.
#[derive(Debug, Clone, Copy, PartialEq, Eq, EnumIsA, EnumAsGetters, VariantName, Serialize, Deserialize)]
pub enum AssumedFunId {
    /// `alloc::boxed::Box::new`
    BoxNew,
    /// `alloc::alloc::box_free`
    /// This is actually an unsafe function, but the rust compiler sometimes
    /// introduces it when going to MIR.
    ///
    /// Also, in practice, deallocation is performed as follows in MIR:
    /// ```text
    /// alloc::alloc::box_free::<T, std::alloc::Global>(
    ///     move (b.0: std::ptr::Unique<T>),
    ///     move (b.1: std::alloc::Global))
    /// ```
    /// When translating from MIR to ULLBC, we do as if the MIR was actually the
    /// following (this is hardcoded - see [crate::register] and [crate::translate_functions_to_ullbc]):
    /// ```text
    /// alloc::alloc::box_free::<T>(move b)
    /// ```
    ///
    /// Also see the comments in [crate::assumed::type_to_used_params].
    BoxFree,
    /// Converted from [ProjectionElem::Index].
    ///
    /// Signature: `fn<T,N>(&[T;N], usize) -> &T`
    ArrayIndexShared,
    /// Converted from [ProjectionElem::Index].
    ///
    /// Signature: `fn<T,N>(&mut [T;N], usize) -> &mut T`
    ArrayIndexMut,
    /// Cast an array as a slice.
    ///
    /// Converted from [UnOp::ArrayToSlice]
    ArrayToSliceShared,
    /// Cast an array as a slice.
    ///
    /// Converted from [UnOp::ArrayToSlice]
    ArrayToSliceMut,
    /// `repeat(n, x)` returns an array where `x` has been replicated `n` times.
    ///
    /// We introduce this when desugaring the [ArrayRepeat] rvalue.
    ArrayRepeat,
    /// Converted from [ProjectionElem::Index].
    ///
    /// Signature: `fn<T>(&[T], usize) -> &T`
    SliceIndexShared,
    /// Converted from [ProjectionElem::Index].
    ///
    /// Signature: `fn<T>(&mut [T], usize) -> &mut T`
    SliceIndexMut,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize, EnumAsGetters)]
pub enum FunIdOrTraitMethodRef {
    Fun(FunId),
    /// If a trait: the reference to the trait and the id of the trait method.
    /// The fun decl id is not really necessary - we put it here for convenience
    /// purposes.
    Trait(TraitRef, TraitItemName, FunDeclId::Id),
}

#[derive(Debug, PartialEq, Eq, Clone, Serialize, Deserialize)]
pub struct FnPtr {
    pub func: FunIdOrTraitMethodRef,
    pub generics: GenericArgs,
    /// If this is a reference to a trait method: stores *all* the generic arguments
    /// which apply to the trait + the method. The fields [region_args], [type_args]
    /// [const_generic_args] only store the arguments which concern the method call.
    /// See the comments for [ParamsInfo].
    pub trait_and_method_generic_args: Option<GenericArgs>,
}

/// A constant expression.
///
/// Only the [Literal] and [Var] cases are left in the final LLBC.
///
/// The other cases come from a straight translation from the MIR:
///
/// [Adt] case:
/// It is a bit annoying, but rustc treats some ADT and tuple instances as
/// constants when generating MIR:
/// - an enumeration with one variant and no fields is a constant.
/// - a structure with no field is a constant.
/// - sometimes, Rust stores the initialization of an ADT as a constant
///   (if all the fields are constant) rather than as an aggregated value
/// We later desugar those to regular ADTs, see [regularize_constant_adts.rs].
///
/// [Global] case: access to a global variable. We later desugar it to
/// a separate statement.
///
/// [Ref] case: reference to a constant value. We later desugar it to a separate
/// statement.
///
/// [FnPtr] case: a function pointer (to a top-level function).
///
/// Remark:
/// MIR seems to forbid more complex expressions like paths. For instance,
/// reading the constant `a.b` is translated to `{ _1 = const a; _2 = (_1.0) }`.
#[derive(Debug, PartialEq, Eq, Clone, Serialize, Deserialize, VariantName, EnumIsA, EnumAsGetters)]
pub enum RawConstantExpr {
    Literal(Literal),
    ///
    /// In most situations:
    /// Enumeration with one variant with no fields, structure with
    /// no fields, unit (encoded as a 0-tuple).
    ///
    /// Less frequently: arbitrary ADT values.
    ///
    /// We eliminate this case in a micro-pass.
    Adt(Option<VariantId::Id>, Vec<ConstantExpr>),
    ///
    /// The value is a top-level value.
    ///
    /// We eliminate this case in a micro-pass.
    Global(GlobalDeclId::Id),
    ///
    /// A trait constant.
    ///
    /// Ex.:
    /// ```text
    /// impl Foo for Bar {
    ///   const C : usize = 32; // <-
    /// }
    /// ```
    ///
    /// Remark: in the generic args, the trait refs are necessarily empty.
    ///
    /// Remark: trait constants can not be used in types, they are necessarily
    /// values. For this reason, we can always erase the regions.
    TraitConst(TraitRef, GenericArgs, TraitItemName),
    ///
    /// A shared reference to a constant value
    ///
    /// We eliminate this case in a micro-pass.
    Ref(Box<ConstantExpr>),
    /// A const generic var
    Var(ConstGenericVarId::Id),
    /// Function pointer
    FnPtr(FnPtr),
}

#[derive(Debug, PartialEq, Eq, Clone, Serialize, Deserialize)]
pub struct ConstantExpr {
    pub value: RawConstantExpr,
    pub ty: Ty,
}

/// TODO: we could factor out [Rvalue] and function calls (for LLBC, not ULLBC).
/// We can also factor out the unops, binops with the function calls.
#[derive(Debug, Clone, Serialize, Deserialize, EnumToGetters, EnumAsGetters, EnumIsA)]
pub enum Rvalue {
    Use(Operand),
    Ref(Place, BorrowKind),
    /// Unary operation (not, neg)
    UnaryOp(UnOp, Operand),
    /// Binary operations (note that we merge "checked" and "unchecked" binops)
    BinaryOp(BinOp, Operand, Operand),
    /// Discriminant (for enumerations).
    /// Note that discriminant values have type isize. We also store the identifier
    /// of the type from which we read the discriminant.
    ///
    /// This case is filtered in [crate::remove_read_discriminant]
    Discriminant(Place, TypeDeclId::Id),
    /// Creates an aggregate value, like a tuple, a struct or an enum:
    /// ```text
    /// l = List::Cons { value:x, tail:tl };
    /// ```
    /// Note that in some MIR passes (like optimized MIR), aggregate values are
    /// decomposed, like below:
    /// ```text
    /// (l as List::Cons).value = x;
    /// (l as List::Cons).tail = tl;
    /// ```
    /// Because we may want to plug our translation mechanism at various
    /// places, we need to take both into accounts in the translation and in
    /// our semantics. Aggregate value initialization is easy, you might want
    /// to have a look at expansion of `Bottom` values for explanations about the
    /// other case.
    ///
    /// Remark: in case of closures, the aggregated value groups the closure id
    /// together with its state.
    Aggregate(AggregateKind, Vec<Operand>),
    /// Not present in MIR: we introduce it when replacing constant variables
    /// in operands in [extract_global_assignments.rs]
    Global(GlobalDeclId::Id),
    /// Length of a memory location. The run-time length of e.g. a vector or a slice is
    /// represented differently (but pretty-prints the same, FIXME).
    /// Should be seen as a function of signature:
    /// - `fn<T;N>(&[T;N]) -> usize`
    /// - `fn<T>(&[T]) -> usize`
    ///
    /// We store the type argument and the const generic (the latter only for arrays).
    ///
    /// [Len] is introduced by rustc for the bound checks: we **eliminate it
    /// together with the bounds checks**. Whenever the user writes `x.len()`
    /// where `x` is a slice or an array, they actually call a non-primitive
    /// function.
    Len(Place, Ty, Option<ConstGeneric>),
    /// [Repeat(x, n)] creates an array where [x] is copied [n] times.
    ///
    /// We desugar this to a function call.
    Repeat(Operand, Ty, ConstGeneric),
}

#[derive(Debug, Clone, VariantIndexArity, Serialize, Deserialize)]
pub enum AggregateKind {
    Adt(TypeId, Option<VariantId::Id>, GenericArgs),
    /// We don't put this with the ADT cas because this is the only assumed type
    /// with aggregates, and it is a primitive type. In particular, it makes
    /// sense to treat it differently because it has a variable number of fields.
    Array(Ty, ConstGeneric),
    /// Aggregated values for closures group the function id together with its
    /// state.
    Closure(FunDeclId::Id, GenericArgs),
}
