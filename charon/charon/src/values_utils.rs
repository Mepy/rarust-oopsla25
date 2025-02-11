//! Implementations for [crate::values]

use crate::types::*;
use crate::values::*;
use serde::{Serialize, Deserialize, Serializer, Deserializer};

impl VarId::Id {
    pub fn to_pretty_string(self) -> String {
        format!("@{self}")
    }
}

#[derive(Debug, Clone)]
pub enum ScalarError {
    /// Attempt to use a signed scalar as an unsigned scalar or vice-versa
    IncorrectSign,
    /// Out of bounds scalar
    OutOfBounds,
}
/// Our redefinition of Result - we don't care much about the I/O part.
pub type ScalarResult<T> = std::result::Result<T, ScalarError>;

impl ScalarValue {
    pub fn get_integer_ty(&self) -> IntegerTy {
        match self {
            ScalarValue::Isize(_) => IntegerTy::Isize,
            ScalarValue::I8(_) => IntegerTy::I8,
            ScalarValue::I16(_) => IntegerTy::I16,
            ScalarValue::I32(_) => IntegerTy::I32,
            ScalarValue::I64(_) => IntegerTy::I64,
            ScalarValue::I128(_) => IntegerTy::I128,
            ScalarValue::Usize(_) => IntegerTy::Usize,
            ScalarValue::U8(_) => IntegerTy::U8,
            ScalarValue::U16(_) => IntegerTy::U16,
            ScalarValue::U32(_) => IntegerTy::U32,
            ScalarValue::U64(_) => IntegerTy::U64,
            ScalarValue::U128(_) => IntegerTy::U128,
        }
    }

    pub fn is_int(&self) -> bool {
        matches!(
            self,
            ScalarValue::Isize(_)
                | ScalarValue::I8(_)
                | ScalarValue::I16(_)
                | ScalarValue::I32(_)
                | ScalarValue::I64(_)
                | ScalarValue::I128(_)
        )
    }

    pub fn is_uint(&self) -> bool {
        matches!(
            self,
            ScalarValue::Usize(_)
                | ScalarValue::U8(_)
                | ScalarValue::U16(_)
                | ScalarValue::U32(_)
                | ScalarValue::U64(_)
                | ScalarValue::U128(_)
        )
    }

    /// When computing the result of binary operations, we convert the values
    /// to u128 then back to the target type (while performing dynamic checks
    /// of course).
    pub fn as_uint(&self) -> ScalarResult<u128> {
        match self {
            ScalarValue::Usize(v) => Ok(*v as u128),
            ScalarValue::U8(v) => Ok(*v as u128),
            ScalarValue::U16(v) => Ok(*v as u128),
            ScalarValue::U32(v) => Ok(*v as u128),
            ScalarValue::U64(v) => Ok(*v as u128),
            ScalarValue::U128(v) => Ok(*v),
            _ => Err(ScalarError::IncorrectSign),
        }
    }

    pub fn uint_is_in_bounds(ty: IntegerTy, v: u128) -> bool {
        match ty {
            IntegerTy::Usize => v <= (usize::MAX as u128),
            IntegerTy::U8 => v <= (u8::MAX as u128),
            IntegerTy::U16 => v <= (u16::MAX as u128),
            IntegerTy::U32 => v <= (u32::MAX as u128),
            IntegerTy::U64 => v <= (u64::MAX as u128),
            IntegerTy::U128 => true,
            _ => false,
        }
    }

    pub fn from_unchecked_uint(ty: IntegerTy, v: u128) -> ScalarValue {
        match ty {
            IntegerTy::Usize => ScalarValue::Usize(v as u64),
            IntegerTy::U8 => ScalarValue::U8(v as u8),
            IntegerTy::U16 => ScalarValue::U16(v as u16),
            IntegerTy::U32 => ScalarValue::U32(v as u32),
            IntegerTy::U64 => ScalarValue::U64(v as u64),
            IntegerTy::U128 => ScalarValue::U128(v),
            _ => panic!("Expected an unsigned integer kind"),
        }
    }

    pub fn from_uint(ty: IntegerTy, v: u128) -> ScalarResult<ScalarValue> {
        if !ScalarValue::uint_is_in_bounds(ty, v) {
            trace!("Not in bounds for {:?}: {}", ty, v);
            Err(ScalarError::OutOfBounds)
        } else {
            Ok(ScalarValue::from_unchecked_uint(ty, v))
        }
    }

    /// When computing the result of binary operations, we convert the values
    /// to i128 then back to the target type (while performing dynamic checks
    /// of course).
    pub fn as_int(&self) -> ScalarResult<i128> {
        match self {
            ScalarValue::Isize(v) => Ok(*v as i128),
            ScalarValue::I8(v) => Ok(*v as i128),
            ScalarValue::I16(v) => Ok(*v as i128),
            ScalarValue::I32(v) => Ok(*v as i128),
            ScalarValue::I64(v) => Ok(*v as i128),
            ScalarValue::I128(v) => Ok(*v),
            _ => Err(ScalarError::IncorrectSign),
        }
    }

    pub fn int_is_in_bounds(ty: IntegerTy, v: i128) -> bool {
        match ty {
            IntegerTy::Isize => v >= (isize::MIN as i128) && v <= (isize::MAX as i128),
            IntegerTy::I8 => v >= (i8::MIN as i128) && v <= (i8::MAX as i128),
            IntegerTy::I16 => v >= (i16::MIN as i128) && v <= (i16::MAX as i128),
            IntegerTy::I32 => v >= (i32::MIN as i128) && v <= (i32::MAX as i128),
            IntegerTy::I64 => v >= (i64::MIN as i128) && v <= (i64::MAX as i128),
            IntegerTy::I128 => true,
            _ => false,
        }
    }

    pub fn from_unchecked_int(ty: IntegerTy, v: i128) -> ScalarValue {
        match ty {
            IntegerTy::Isize => ScalarValue::Isize(v as i64),
            IntegerTy::I8 => ScalarValue::I8(v as i8),
            IntegerTy::I16 => ScalarValue::I16(v as i16),
            IntegerTy::I32 => ScalarValue::I32(v as i32),
            IntegerTy::I64 => ScalarValue::I64(v as i64),
            IntegerTy::I128 => ScalarValue::I128(v),
            _ => panic!("Expected a signed integer kind"),
        }
    }

    pub fn from_le_bytes(ty: IntegerTy, b: [u8; 16]) -> ScalarValue {
        use std::convert::TryInto;
        match ty {
            IntegerTy::Isize => {
                let b: [u8; 8] = b[0..8].try_into().unwrap();
                ScalarValue::Isize(i64::from_le_bytes(b))
            }
            IntegerTy::I8 => {
                let b: [u8; 1] = b[0..1].try_into().unwrap();
                ScalarValue::I8(i8::from_le_bytes(b))
            }
            IntegerTy::I16 => {
                let b: [u8; 2] = b[0..2].try_into().unwrap();
                ScalarValue::I16(i16::from_le_bytes(b))
            }
            IntegerTy::I32 => {
                let b: [u8; 4] = b[0..4].try_into().unwrap();
                ScalarValue::I32(i32::from_le_bytes(b))
            }
            IntegerTy::I64 => {
                let b: [u8; 8] = b[0..8].try_into().unwrap();
                ScalarValue::I64(i64::from_le_bytes(b))
            }
            IntegerTy::I128 => {
                let b: [u8; 16] = b[0..16].try_into().unwrap();
                ScalarValue::I128(i128::from_le_bytes(b))
            }
            IntegerTy::Usize => {
                let b: [u8; 8] = b[0..8].try_into().unwrap();
                ScalarValue::Usize(u64::from_le_bytes(b))
            }
            IntegerTy::U8 => {
                let b: [u8; 1] = b[0..1].try_into().unwrap();
                ScalarValue::U8(u8::from_le_bytes(b))
            }
            IntegerTy::U16 => {
                let b: [u8; 2] = b[0..2].try_into().unwrap();
                ScalarValue::U16(u16::from_le_bytes(b))
            }
            IntegerTy::U32 => {
                let b: [u8; 4] = b[0..4].try_into().unwrap();
                ScalarValue::U32(u32::from_le_bytes(b))
            }
            IntegerTy::U64 => {
                let b: [u8; 8] = b[0..8].try_into().unwrap();
                ScalarValue::U64(u64::from_le_bytes(b))
            }
            IntegerTy::U128 => {
                let b: [u8; 16] = b[0..16].try_into().unwrap();
                ScalarValue::U128(u128::from_le_bytes(b))
            }
        }
    }

    /// **Warning**: most constants are stored as u128 by rustc. When converting
    /// to i128, it is not correct to do `v as i128`, we must reinterpret the
    /// bits (see [ScalarValue::from_le_bytes]).
    pub fn from_int(ty: IntegerTy, v: i128) -> ScalarResult<ScalarValue> {
        if !ScalarValue::int_is_in_bounds(ty, v) {
            Err(ScalarError::OutOfBounds)
        } else {
            Ok(ScalarValue::from_unchecked_int(ty, v))
        }
    }
}

impl std::fmt::Display for ScalarValue {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::result::Result<(), std::fmt::Error> {
        match self {
            ScalarValue::Isize(v) => write!(f, "{v} : isize"),
            ScalarValue::I8(v) => write!(f, "{v} : i8"),
            ScalarValue::I16(v) => write!(f, "{v} : i16"),
            ScalarValue::I32(v) => write!(f, "{v} : i32"),
            ScalarValue::I64(v) => write!(f, "{v} : i64"),
            ScalarValue::I128(v) => write!(f, "{v} : i128"),
            ScalarValue::Usize(v) => write!(f, "{v} : usize"),
            ScalarValue::U8(v) => write!(f, "{v} : u8"),
            ScalarValue::U16(v) => write!(f, "{v} : u16"),
            ScalarValue::U32(v) => write!(f, "{v} : u32"),
            ScalarValue::U64(v) => write!(f, "{v} : u64"),
            ScalarValue::U128(v) => write!(f, "{v} : u128"),
        }
    }
}

impl std::fmt::Display for Literal {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::result::Result<(), std::fmt::Error> {
        match self {
            Literal::Scalar(v) => write!(f, "{v}"),
            Literal::Bool(v) => write!(f, "{v}"),
            Literal::Char(v) => write!(f, "{v}"),
        }
    }
}

#[derive(Serialize, Deserialize)]
enum ScalarValueString {
    /// Using i64 to be safe
    Isize(String),
    I8(String),
    I16(String),
    I32(String),
    I64(String),
    I128(String),
    /// Using u64 to be safe
    Usize(String),
    U8(String),
    U16(String),
    U32(String),
    U64(String),
    U128(String),
}
impl From<ScalarValue> for ScalarValueString
{
    fn from(value: ScalarValue) -> Self {
        match value
        {
        | ScalarValue::Isize(n) => ScalarValueString::Isize(n.to_string()),
        | ScalarValue::I8(n) => ScalarValueString::I8(n.to_string()),
        | ScalarValue::I16(n) => ScalarValueString::I16(n.to_string()),
        | ScalarValue::I32(n) => ScalarValueString::I32(n.to_string()),
        | ScalarValue::I64(n) => ScalarValueString::I64(n.to_string()),
        | ScalarValue::I128(n) => ScalarValueString::I128(n.to_string()),
        | ScalarValue::Usize(n) => ScalarValueString::Usize(n.to_string()),
        | ScalarValue::U8(n) => ScalarValueString::U8(n.to_string()),
        | ScalarValue::U16(n) => ScalarValueString::U16(n.to_string()),
        | ScalarValue::U32(n) => ScalarValueString::U32(n.to_string()),
        | ScalarValue::U64(n) => ScalarValueString::U64(n.to_string()),
        | ScalarValue::U128(n) => ScalarValueString::U128(n.to_string()),
        }
    }
}
impl From<ScalarValueString> for ScalarValue
{
    fn from(value: ScalarValueString) -> Self {
        match value
        {
        | ScalarValueString::Isize(n) => ScalarValue::Isize(n.parse::<i64>().unwrap()),
        | ScalarValueString::I8(n) => ScalarValue::I8(n.parse::<i8>().unwrap()),
        | ScalarValueString::I16(n) => ScalarValue::I16(n.parse::<i16>().unwrap()),
        | ScalarValueString::I32(n) => ScalarValue::I32(n.parse::<i32>().unwrap()),
        | ScalarValueString::I64(n) => ScalarValue::I64(n.parse::<i64>().unwrap()),
        | ScalarValueString::I128(n) => ScalarValue::I128(n.parse::<i128>().unwrap()),
        | ScalarValueString::Usize(n) => ScalarValue::Usize(n.parse::<u64>().unwrap()),
        | ScalarValueString::U8(n) => ScalarValue::U8(n.parse::<u8>().unwrap()),
        | ScalarValueString::U16(n) => ScalarValue::U16(n.parse::<u16>().unwrap()),
        | ScalarValueString::U32(n) => ScalarValue::U32(n.parse::<u32>().unwrap()),
        | ScalarValueString::U64(n) => ScalarValue::U64(n.parse::<u64>().unwrap()),
        | ScalarValueString::U128(n) => ScalarValue::U128(n.parse::<u128>().unwrap()),
        }
    }
}

impl Serialize for ScalarValue {
    fn serialize<S>(&self, serializer: S) -> std::result::Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        let scalar_string = ScalarValueString::from(*self);
        scalar_string.serialize(serializer)
    }
}

impl<'de> Deserialize<'de> for ScalarValue 
{
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        let scalar_string = ScalarValueString::deserialize(deserializer)?;
        Ok(ScalarValue::from(scalar_string))
    }
}