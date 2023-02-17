//
// type.h
//
// Copyright (c) 2020-2023 Peter Niekamp. All rights reserved.
//
// This file is part of zaalang, which is BSD-2-Clause licensed.
// See http://opensource.org/licenses/BSD-2-Clause
//

#pragma once

#include "decl.h"
#include "ident.h"
#include <string>
#include <string_view>
#include <vector>
#include <unordered_map>
#include <algorithm>

//-------------------------- Type -------------------------------------------
//---------------------------------------------------------------------------

class Type
{
  public:

    enum Klass
    {
      Builtin,
      Const,
      Pointer,
      Reference,
      Slice,
      Array,
      Tuple,
      TypeRef,
      TypeArg,
      QualArg,
      TypeLit,
      Tag,
      Constant,
      Function,
      Pack,
      Unpack,
    };

    enum Flags
    {
      Concrete = 0x1,
      Resolved = 0x2,
      Unresolved = 0x4,
      ZeroSized = 0x8,
      TrivialCopy = 0x10,
      TrivialAssign = 0x20,
      TrivialDestroy = 0x40,
      LiteralCopy = 0x080,
      Packed = 0x100,
    };

    long flags = 0;

  public:
    Type(Klass klass);

    Klass klass() const { return m_klass; }

    virtual void dump(int indent) const = 0;

  protected:

    Klass m_klass;
};


//-------------------------- BuiltinType ------------------------------------
//---------------------------------------------------------------------------

class BuiltinType : public Type
{
  public:

    enum Kind
    {
      Void,
      Bool,
      Char,
      I8, I16, I32, I64, ISize,
      U8, U16, U32, U64, USize,
      F32, F64,
      IntLiteral,
      FloatLiteral,
      StringLiteral,
      DeclidLiteral,
      TypeidLiteral,
      PtrLiteral,
    };

    static Ident *builtintype_idents[];

    static Ident *name(Kind kind) { return builtintype_idents[kind]; }

  public:
    BuiltinType(Kind kind);

    Kind kind() const { return m_kind; }
    Ident *name() const { return name(m_kind); }

    bool is_void_type() const
    {
      return m_kind == Void;
    }

    bool is_int_type() const
    {
      return m_kind == I8 || m_kind == I16 || m_kind == I32 || m_kind == I64 || m_kind == ISize || m_kind == U8 || m_kind == U16 || m_kind == U32 || m_kind == U64 || m_kind == USize || m_kind == IntLiteral;
    }

    bool is_float_type() const
    {
      return m_kind == F32 || m_kind == F64 || m_kind == FloatLiteral;
    }

    bool is_char_type() const
    {
      return m_kind == Char;
    }

    bool is_bool_type() const
    {
      return m_kind == Bool;
    }

    bool is_signed_type() const
    {
      return m_kind == I8 || m_kind == I16 || m_kind == I32 || m_kind == I64 || m_kind == ISize || m_kind == F32 || m_kind == F64 || m_kind == IntLiteral || m_kind == FloatLiteral;
    }

    void dump(int indent) const override;

  protected:

    Kind m_kind;
};

bool is_literal_valid(BuiltinType::Kind kind, Numeric::Int const &value);
bool is_literal_valid(BuiltinType::Kind kind, Numeric::Float const &value);


//-------------------------- ConstType --------------------------------------
//---------------------------------------------------------------------------

class ConstType : public Type
{
  public:
    ConstType(Type *type);

    Type *type;

    void dump(int indent) const override;
};


//-------------------------- PointerType ------------------------------------
//---------------------------------------------------------------------------

class PointerType : public Type
{
  public:
    PointerType(Type *type);

    Type *type;

    void dump(int indent) const override;
};


//-------------------------- ReferenceType ----------------------------------
//---------------------------------------------------------------------------

class ReferenceType : public Type
{
  public:
    ReferenceType(Type *type);

    Type *type;

    void dump(int indent) const override;
};


//-------------------------- SliceType --------------------------------------
//---------------------------------------------------------------------------

class SliceType : public Type
{
  public:
    SliceType(Type *type);

    Type *type;

    void dump(int indent) const override;
};


//-------------------------- ArrayType --------------------------------------
//---------------------------------------------------------------------------

class ArrayType : public Type
{
  public:
    ArrayType(Type *type, Type *size);

    Type *type;
    Type *size;

    void dump(int indent) const override;
};

size_t array_len(ArrayType const *type);


//-------------------------- CompoundType -----------------------------------
//---------------------------------------------------------------------------

class CompoundType : public Type
{
  public:
    CompoundType(Klass klass);
    CompoundType(Klass klass, std::vector<Type*> &&resolved_fields);

    std::vector<Type*> fields;
};


//-------------------------- TupleType --------------------------------------
//---------------------------------------------------------------------------

class TupleType : public CompoundType
{
  public:
    TupleType(std::vector<Type*> const &fields);
    TupleType(std::vector<Type*> &&resolved_defns, std::vector<Type*> &&resolved_fields);

    std::vector<Type*> defns;

    void dump(int indent) const override;
};

size_t tuple_len(TupleType const *type);


//-------------------------- TypeArgType ------------------------------------
//---------------------------------------------------------------------------

class TypeArgType : public Type
{
  public:
    TypeArgType(Decl *decl);
    TypeArgType(Decl *decl, Decl *koncept, std::vector<std::pair<Decl*, Type*>> const &args = {});

    Decl *decl;

    Decl *koncept = nullptr;
    std::vector<std::pair<Decl*, Type*>> args;

    void dump(int indent) const override;
};


//-------------------------- QualArgType ------------------------------------
//---------------------------------------------------------------------------

class QualArgType : public Type
{
  public:

    enum Qualifiers
    {
      Const = 0x1,
      RValue = 0x2,
    };

    long qualifiers = 0;

  public:
    QualArgType(Type *type, long qualifiers = 0);

    Type *type;

    void dump(int indent) const override;
};


//-------------------------- TypeLitType ------------------------------------
//---------------------------------------------------------------------------

class TypeLitType : public Type
{
  public:
    TypeLitType(Expr *value);

    Expr *value;

    void dump(int indent) const override;
};

bool equals(TypeLitType *lhs, Expr *rhs);
bool equals(TypeLitType *lhs, TypeLitType *rhs);


//-------------------------- ConstantType -----------------------------------
//---------------------------------------------------------------------------

class ConstantType : public Type
{
  public:
    ConstantType(Decl *decl, Type *type);

    Decl *decl;
    Type *type;
    Type *expr = nullptr;

    void resolve(Type *resolved_expr);

    void dump(int indent) const override;
};


//-------------------------- TypeRefType ------------------------------------
//---------------------------------------------------------------------------

class TypeRefType : public Type
{
  public:
    TypeRefType(Decl *decl);

    Decl *decl;
    std::vector<std::pair<Decl*, Type*>> args;

    void dump(int indent) const override;
};


//-------------------------- TagType ----------------------------------------
//---------------------------------------------------------------------------

class TagType : public CompoundType
{
  public:
    TagType(Decl *decl, std::vector<std::pair<Decl*, Type*>> const &args);

    Decl *decl;
    std::vector<std::pair<Decl*, Type*>> args;

    std::vector<Decl*> decls;
    std::vector<Decl*> fieldvars;

    void resolve(std::vector<Decl*> &&resolved_decls);
    void resolve(std::vector<Type*> &&resolved_fields);

    void dump(int indent) const override;
};


//-------------------------- FunctionType -----------------------------------
//---------------------------------------------------------------------------

class FunctionType : public Type
{
  public:
    FunctionType(Type *returntype, Type *paramtuple, Type *throwtype = nullptr);

    Type *returntype;
    Type *paramtuple;
    Type *throwtype;

    void dump(int indent) const override;
};


//-------------------------- PackType ---------------------------------------
//---------------------------------------------------------------------------

class PackType : public Type
{
  public:
    PackType(Type *type);

    Type *type;

    void dump(int indent) const override;
};


//-------------------------- UnpackType -------------------------------------
//---------------------------------------------------------------------------

class UnpackType : public Type
{
  public:
    UnpackType(Type *type);

    Type *type;

    void dump(int indent) const override;
};


//
// misc functions
//

bool is_void_type(Type const *type);
bool is_int_type(Type const *type);
bool is_float_type(Type const *type);
bool is_char_type(Type const *type);
bool is_string_type(Type const *type);
bool is_bool_type(Type const *type);
bool is_null_type(Type const *type);
bool is_declid_type(Type const *type);
bool is_typeid_type(Type const *type);
bool is_signed_type(Type const *type);

bool is_const_type(Type const *type);
bool is_const_pointer(Type const *type);
bool is_const_reference(Type const *type);
bool is_builtin_type(Type const *type);
bool is_pointer_type(Type const *type);
bool is_reference_type(Type const *type);
bool is_typearg_type(Type const *type);
bool is_qualarg_type(Type const *type);
bool is_qualarg_reference(Type const *type);
bool is_typelit_type(Type const *type);
bool is_array_type(Type const *type);
bool is_slice_type(Type const *type);
bool is_tuple_type(Type const *type);
bool is_function_type(Type const *type);

bool is_pack_type(Type const *type);
bool is_unpack_type(Type const *type);

bool is_tag_type(Type const *type);
bool is_struct_type(Type const *type);
bool is_union_type(Type const *type);
bool is_vtable_type(Type const *type);
bool is_lambda_type(Type const *type);
bool is_enum_type(Type const *type);

bool is_compound_type(Type const *type);

bool is_concrete_type(Type const *type);
bool is_resolved_type(Type const *type);
bool is_unresolved_type(Type const *type);
bool is_zerosized_type(Type const *type);
bool is_trivial_copy_type(Type const *type);
bool is_trivial_assign_type(Type const *type);
bool is_trivial_destroy_type(Type const *type);
bool is_literal_copy_type(Type const *type);

Type *remove_const_type(Type *type);
Type const *remove_const_type(Type const *type);

Type *remove_pointer_type(Type *type);
Type const *remove_pointer_type(Type const *type);

Type *remove_reference_type(Type *type);
Type const *remove_reference_type(Type const *type);

bool is_voidpointer_type(Type const *type);
bool is_pointference_type(Type const *type);

Type *remove_pointference_type(Type *type);
Type const *remove_pointference_type(Type const *type);

Type const *remove_qualifiers_type(Type const *type);
Type *remove_qualifiers_type(Type *type);

size_t sizeof_type(Type const *type);
size_t alignof_type(Type const *type);
size_t sizeof_field(CompoundType const *type, size_t index);
size_t alignof_field(CompoundType const *type, size_t index);
size_t offsetof_field(CompoundType const *type, size_t index);

std::ostream &operator <<(std::ostream &os, Type const &type);


// checked casts

template<typename T> auto type_cast(Type *);
template<> inline auto type_cast<BuiltinType>(Type *type) { assert(type && type->klass() == Type::Builtin); return static_cast<BuiltinType*>(type); };
template<> inline auto type_cast<ConstType>(Type *type) { assert(type && type->klass() == Type::Const); return static_cast<ConstType*>(type); };
template<> inline auto type_cast<PointerType>(Type *type) { assert(type && type->klass() == Type::Pointer); return static_cast<PointerType*>(type); };
template<> inline auto type_cast<ReferenceType>(Type *type) { assert(type && type->klass() == Type::Reference); return static_cast<ReferenceType*>(type); };
template<> inline auto type_cast<SliceType>(Type *type) { assert(type && type->klass() == Type::Slice); return static_cast<SliceType*>(type); };
template<> inline auto type_cast<ArrayType>(Type *type) { assert(type && type->klass() == Type::Array); return static_cast<ArrayType*>(type); };
template<> inline auto type_cast<TupleType>(Type *type) { assert(type && type->klass() == Type::Tuple); return static_cast<TupleType*>(type); };
template<> inline auto type_cast<TypeRefType>(Type *type) { assert(type && type->klass() == Type::TypeRef); return static_cast<TypeRefType*>(type); };
template<> inline auto type_cast<TypeArgType>(Type *type) { assert(type && type->klass() == Type::TypeArg); return static_cast<TypeArgType*>(type); };
template<> inline auto type_cast<QualArgType>(Type *type) { assert(type && type->klass() == Type::QualArg); return static_cast<QualArgType*>(type); };
template<> inline auto type_cast<TypeLitType>(Type *type) { assert(type && type->klass() == Type::TypeLit); return static_cast<TypeLitType*>(type); };
template<> inline auto type_cast<ConstantType>(Type *type) { assert(type && type->klass() == Type::Constant); return static_cast<ConstantType*>(type); };
template<> inline auto type_cast<TagType>(Type *type) { assert(type && type->klass() == Type::Tag); return static_cast<TagType*>(type); };
template<> inline auto type_cast<FunctionType>(Type *type) { assert(type && type->klass() == Type::Function); return static_cast<FunctionType*>(type); };
template<> inline auto type_cast<PackType>(Type *type) { assert(type && type->klass() == Type::Pack); return static_cast<PackType *>(type); };
template<> inline auto type_cast<UnpackType>(Type *type) { assert(type && type->klass() == Type::Unpack); return static_cast<UnpackType *>(type); };
template<> inline auto type_cast<CompoundType>(Type *type) { assert(type && is_compound_type(type)); return static_cast<CompoundType*>(type); };

template<typename T> auto type_cast(Type const *);
template<> inline auto type_cast<BuiltinType>(Type const *type) { assert(type && type->klass() == Type::Builtin); return static_cast<BuiltinType const *>(type); };
template<> inline auto type_cast<ConstType>(Type const *type) { assert(type && type->klass() == Type::Const); return static_cast<ConstType const *>(type); };
template<> inline auto type_cast<PointerType>(Type const *type) { assert(type && type->klass() == Type::Pointer); return static_cast<PointerType const *>(type); };
template<> inline auto type_cast<ReferenceType>(Type const *type) { assert(type && type->klass() == Type::Reference); return static_cast<ReferenceType const *>(type); };
template<> inline auto type_cast<SliceType>(Type const *type) { assert(type && type->klass() == Type::Slice); return static_cast<SliceType const *>(type); };
template<> inline auto type_cast<ArrayType>(Type const *type) { assert(type && type->klass() == Type::Array); return static_cast<ArrayType const *>(type); };
template<> inline auto type_cast<TupleType>(Type const *type) { assert(type && type->klass() == Type::Tuple); return static_cast<TupleType const *>(type); };
template<> inline auto type_cast<TypeRefType>(Type const *type) { assert(type && type->klass() == Type::TypeRef); return static_cast<TypeRefType const *>(type); };
template<> inline auto type_cast<TypeArgType>(Type const *type) { assert(type && type->klass() == Type::TypeArg); return static_cast<TypeArgType const *>(type); };
template<> inline auto type_cast<QualArgType>(Type const *type) { assert(type && type->klass() == Type::QualArg); return static_cast<QualArgType const *>(type); };
template<> inline auto type_cast<TypeLitType>(Type const *type) { assert(type && type->klass() == Type::TypeLit); return static_cast<TypeLitType const *>(type); };
template<> inline auto type_cast<ConstantType>(Type const *type) { assert(type && type->klass() == Type::Constant); return static_cast<ConstantType const *>(type); };
template<> inline auto type_cast<TagType>(Type const *type) { assert(type && type->klass() == Type::Tag); return static_cast<TagType const *>(type); };
template<> inline auto type_cast<FunctionType>(Type const *type) { assert(type && type->klass() == Type::Function); return static_cast<FunctionType const *>(type); };
template<> inline auto type_cast<PackType>(Type const *type) { assert(type && type->klass() == Type::Pack); return static_cast<PackType const *>(type); };
template<> inline auto type_cast<UnpackType>(Type const *type) { assert(type && type->klass() == Type::Unpack); return static_cast<UnpackType const *>(type); };
template<> inline auto type_cast<CompoundType>(Type const *type) { assert(type && is_compound_type(type)); return static_cast<CompoundType const *>(type); };
