//
// builtins.h
//
// Copyright (c) 2020-2024 Peter Niekamp. All rights reserved.
//
// This file is part of zaalang, which is BSD-2-Clause licensed.
// See http://opensource.org/licenses/BSD-2-Clause
//

#pragma once

#include <vector>
#include <string_view>

class AST;
class Decl;
class Type;
class FnSig;

//---------------------- Builtins -------------------------------------------
//---------------------------------------------------------------------------

namespace Builtin
{
  enum Kind : int
  {
    Type_Void,
    Type_Bool,
    Type_Char,
    Type_I8,
    Type_I16,
    Type_I32,
    Type_I64,
    Type_ISize,
    Type_U8,
    Type_U16,
    Type_U32,
    Type_U64,
    Type_USize,
    Type_F32,
    Type_F64,

    Type_Ptr,
    Type_Ref,
    Type_Enum,
    Type_Lit,

    Type_IntLiteral,
    Type_FloatLiteral,
    Type_StringLiteral,
    Type_DeclidLiteral,
    Type_TypeidLiteral,
    Type_PtrLiteral,

    Default_Constructor,
    Default_Copytructor,
    Default_Assignment,
    Default_Equality,
    Default_Compare,
    Default_Destructor,

    Array_Constructor,
    Array_Copytructor,
    Array_Assignment,
    Array_Destructor,

    Tuple_Constructor,
    Tuple_Inittructor,
    Tuple_Copytructor,
    Tuple_CopytructorEx,
    Tuple_Assignment,
    Tuple_AssignmentEx,
    Tuple_Destructor,

    Literal_Copytructor,
    Literal_Assignment,

    VTable_Constructor,

    Builtin_Destructor,

    Plus,
    Minus,
    Not,
    LNot,
    PreInc,
    PreDec,
    DeRef,
    Range,

    Add,
    Sub,
    Div,
    Mul,
    Rem,
    Shl,
    Shr,
    And,
    Or,
    Xor,
    LAnd,
    LOr,
    LT,
    GT,
    LE,
    GE,
    EQ,
    NE,
    Cmp,
    Assign,
    MulAssign,
    DivAssign,
    RemAssign,
    AddAssign,
    SubAssign,
    ShlAssign,
    ShrAssign,
    AndAssign,
    XorAssign,
    OrAssign,
    AddCarry,
    SubBorrow,
    MulCarry,

    OffsetAdd,
    OffsetSub,
    Difference,
    OffsetAddAssign,
    OffsetSubAssign,

    ArrayLen,
    ArrayData,
    ArrayIndex,
    ArrayBegin,
    ArrayEnd,
    ArrayEq,
    ArrayCmp,
    ArrayCreate,

    TupleLen,
    TupleEq,
    TupleEqEx,
    TupleCmp,
    TupleCmpEx,

    StringLen,
    StringData,
    StringIndex,
    StringBegin,
    StringEnd,
    StringSlice,
    StringAppend,
    StringCreate,

    SliceLen,
    SliceData,
    SliceIndex,
    SliceBegin,
    SliceEnd,
    SliceSlice,

    MatchRange,
    MatchRangeEq,

    Bool,

    CallOp,

    is_same,
    is_const,
    is_rvalue,
    is_match,
    is_enum,
    is_array,
    is_tuple,
    is_union,
    is_struct,
    is_vtable,
    is_lambda,
    is_slice,
    is_builtin,
    is_pointer,
    is_reference,
    is_instance,
    is_trivial_copy,
    is_trivial_assign,
    is_trivial_destroy,
    is_const_eval,
    tuple_len,
    array_len,

    is_nan,
    is_finite,
    is_normal,
    nan,
    inf,

    is_integral,
    is_unsigned,
    is_floating_point,
    is_arithmetic,

    clz,
    ctz,
    popcnt,
    signbit,
    byteswap,
    bitreverse,

    abs,
    min,
    max,
    floor,
    ceil,
    round,
    trunc,
    copysign,
    frexp,
    ldexp,
    sqrt,

    memset,
    memcpy,
    memmove,
    memfind,

    alloca,

    symbol,

    atomic_load,
    atomic_store,
    atomic_xchg,
    atomic_cmpxchg,

    atomic_fetch_add,
    atomic_fetch_sub,
    atomic_fetch_and,
    atomic_fetch_xor,
    atomic_fetch_or,
    atomic_fetch_nand,

    atomic_thread_fence,

    rdtsc,
    rdtscp,
    relax,
    inline_asm,

    decl_kind,
    decl_name,
    decl_flags,
    decl_parent,
    decl_children,
    decl_site,
    decl_attr,
    attr_text,
    type_decl,
    type_name,
    type_children,
    type_query,

    __argc__,
    __argv__,
    __envp__,

    __site__,
    __decl__,
    __function__,
    __module__,

    __cfg,
    __cfg__,
    __srcdir__,
    __bindir__,

    Module,
  };

  auto type(Kind kind) -> Type *;

  auto fn(Decl *module, Builtin::Kind kind, Type *T1 = nullptr, Type *T2 = nullptr) -> FnSig;

  auto where(Decl *decl, std::vector<std::pair<Decl*, Type*>> const &typeargs) -> bool;
};

Decl *make_builtin_module(AST *ast);
