//
// type.cpp
//
// Copyright (c) 2020-2024 Peter Niekamp. All rights reserved.
//
// This file is part of zaalang, which is BSD-2-Clause licensed.
// See http://opensource.org/licenses/BSD-2-Clause
//

#include "ast.h"
#include <iostream>
#include <limits>
#include <cassert>

using namespace std;

Ident *BuiltinType::builtintype_idents[] = {
  /* Void,          */ Ident::from("void"),
  /* Bool,          */ Ident::from("bool"),
  /* Char,          */ Ident::from("char"),
  /* I8,            */ Ident::from("i8"),
  /* I16,           */ Ident::from("i16"),
  /* I32,           */ Ident::from("i32"),
  /* I64,           */ Ident::from("i64"),
  /* ISize,         */ Ident::from("isize"),
  /* U8,            */ Ident::from("u8"),
  /* U16,           */ Ident::from("u16"),
  /* U32,           */ Ident::from("u32"),
  /* U64,           */ Ident::from("u64"),
  /* USize,         */ Ident::from("usize"),
  /* F32,           */ Ident::from("f32"),
  /* F64,           */ Ident::from("f64"),
  /* IntLiteral,    */ Ident::from("#int"),
  /* FloatLiteral,  */ Ident::from("#float"),
  /* StringLiteral, */ Ident::from("#string"),
  /* DeclidLiteral, */ Ident::from("#declid"),
  /* TypeidLiteral, */ Ident::from("#typeid"),
  /* PtrLiteral,    */ Ident::from("null"),
};

namespace
{
  struct spaces
  {
    spaces(int n)
      : n(n)
    {
    }

    friend ostream &operator <<(ostream &os, spaces const &indent)
    {
      for (int i = 0; i < indent.n; ++i)
        os << ' ';

      return os;
    }

    int n;
  };
}

//|///////////////////// is_void_type ///////////////////////////////////////
bool is_void_type(Type const *type)
{
  return type->klass() == Type::Builtin && type_cast<BuiltinType>(type)->is_void_type();
}

//|///////////////////// is_int_type ////////////////////////////////////////
bool is_int_type(Type const *type)
{
  return type->klass() == Type::Builtin && type_cast<BuiltinType>(type)->is_int_type();
}

//|///////////////////// is_float_type /////////////////////////////////////
bool is_float_type(Type const *type)
{
  return type->klass() == Type::Builtin && type_cast<BuiltinType>(type)->is_float_type();
}

//|///////////////////// is_char_type ///////////////////////////////////////
bool is_char_type(Type const *type)
{
  return type->klass() == Type::Builtin && type_cast<BuiltinType>(type)->is_char_type();
}

//|///////////////////// is_string_type /////////////////////////////////////
bool is_string_type(Type const *type)
{
  return type->klass() == Type::Builtin && type_cast<BuiltinType>(type)->kind() == BuiltinType::StringLiteral;
}

//|///////////////////// is_bool_type ///////////////////////////////////////
bool is_bool_type(Type const *type)
{
  return type->klass() == Type::Builtin && type_cast<BuiltinType>(type)->is_bool_type();
}

//|///////////////////// is_null_type ///////////////////////////////////////
bool is_null_type(Type const *type)
{
  return type->klass() == Type::Builtin && type_cast<BuiltinType>(type)->kind() == BuiltinType::PtrLiteral;
}

//|///////////////////// is_declid_type /////////////////////////////////////
bool is_declid_type(Type const *type)
{
  return type->klass() == Type::Builtin && type_cast<BuiltinType>(type)->kind() == BuiltinType::DeclidLiteral;
}

//|///////////////////// is_typeid_type /////////////////////////////////////
bool is_typeid_type(Type const *type)
{
  return type->klass() == Type::Builtin && type_cast<BuiltinType>(type)->kind() == BuiltinType::TypeidLiteral;
}

//|///////////////////// is_signed_type /////////////////////////////////////
bool is_signed_type(Type const *type)
{
  return type->klass() == Type::Builtin && type_cast<BuiltinType>(type)->is_signed_type();
}

//|///////////////////// is_const_type //////////////////////////////////////
bool is_const_type(Type const *type)
{
  return type->klass() == Type::Const;
}

//|///////////////////// is_const_pointer ///////////////////////////////////
bool is_const_pointer(Type const *type)
{
  return type->klass() == Type::Pointer && type_cast<PointerType>(type)->type->klass() == Type::Const;
}

//|///////////////////// is_const_reference /////////////////////////////////
bool is_const_reference(Type const *type)
{
  return type->klass() == Type::Reference && type_cast<ReferenceType>(type)->type->klass() == Type::Const;
}

//|///////////////////// is_builtin_type ////////////////////////////////////
bool is_builtin_type(Type const *type)
{
  return type->klass() == Type::Builtin;
}

//|///////////////////// is_pointer_type ////////////////////////////////////
bool is_pointer_type(Type const *type)
{
  return type->klass() == Type::Pointer;
}

//|///////////////////// is_reference_type //////////////////////////////////
bool is_reference_type(Type const *type)
{
  return type->klass() == Type::Reference;
}

//|///////////////////// is_typearg_type ////////////////////////////////////
bool is_typearg_type(Type const *type)
{
  return type->klass() == Type::TypeArg;
}

//|///////////////////// is_qualarg_type ////////////////////////////////////
bool is_qualarg_type(Type const *type)
{
  return type->klass() == Type::QualArg;
}

//|///////////////////// is_qualarg_reference ///////////////////////////////
bool is_qualarg_reference(Type const *type)
{
  return type->klass() == Type::Reference && type_cast<ReferenceType>(type)->type->klass() == Type::QualArg;
}

//|///////////////////// is_typelit_type ////////////////////////////////////
bool is_typelit_type(Type const *type)
{
  return type->klass() == Type::TypeLit;
}

//|///////////////////// is_slice_type //////////////////////////////////////
bool is_slice_type(Type const *type)
{
  return type->klass() == Type::Slice;
}

//|///////////////////// is_array_type //////////////////////////////////////
bool is_array_type(Type const *type)
{
  return type->klass() == Type::Array;
}

//|///////////////////// is_tuple_type //////////////////////////////////////
bool is_tuple_type(Type const *type)
{
  return type->klass() == Type::Tuple;
}

//|///////////////////// is_function_type ///////////////////////////////////
bool is_function_type(Type const *type)
{
  return type->klass() == Type::Function;
}

//|///////////////////// is_pack_type ///////////////////////////////////////
bool is_pack_type(Type const *type)
{
  return type->klass() == Type::Pack;
}

//|///////////////////// is_unpack_type /////////////////////////////////////
bool is_unpack_type(Type const *type)
{
  return type->klass() == Type::Unpack;
}

//|///////////////////// is_tag_type ////////////////////////////////////////
bool is_tag_type(Type const *type)
{
  return type->klass() == Type::Tag;
}

//|///////////////////// is_struct_type /////////////////////////////////////
bool is_struct_type(Type const *type)
{
  return is_tag_type(type) && type_cast<TagType>(type)->decl->kind() == Decl::Struct;
}

//|///////////////////// is_union_type //////////////////////////////////////
bool is_union_type(Type const *type)
{
  return is_tag_type(type) && type_cast<TagType>(type)->decl->kind() == Decl::Union;
}

//|///////////////////// is_vtable_type /////////////////////////////////////
bool is_vtable_type(Type const *type)
{
  return is_tag_type(type) && type_cast<TagType>(type)->decl->kind() == Decl::VTable;
}

//|///////////////////// is_lambda_type /////////////////////////////////////
bool is_lambda_type(Type const *type)
{
  return is_tag_type(type) && type_cast<TagType>(type)->decl->kind() == Decl::Lambda;
}

//|///////////////////// is_enum_type ///////////////////////////////////////
bool is_enum_type(Type const *type)
{
  return is_tag_type(type) && type_cast<TagType>(type)->decl->kind() == Decl::Enum;
}

//|///////////////////// is_compound_type ///////////////////////////////////
bool is_compound_type(Type const *type)
{
  return is_tuple_type(type) || is_struct_type(type) || is_union_type(type) || is_vtable_type(type) || is_lambda_type(type);
}

//|///////////////////// is_concrete_type ///////////////////////////////////
bool is_concrete_type(Type const *type)
{
  return type->flags & Type::Concrete;
}

//|///////////////////// is_indefinite_type /////////////////////////////////
bool is_indefinite_type(Type const *type)
{
  return type->flags & Type::Indefinite;
}

//|///////////////////// is_unresolved_type /////////////////////////////////
bool is_unresolved_type(Type const *type)
{
  return type->flags & Type::Unresolved;
}

//|///////////////////// is_unresolved_type /////////////////////////////////
bool is_incomplete_type(Type const *type)
{
  return type->flags & Type::Incomplete;
}

//|///////////////////// is_zerosized_type //////////////////////////////////
bool is_zerosized_type(Type const *type)
{
  return type->flags & Type::ZeroSized;
}

//|///////////////////// is_trivial_type ////////////////////////////////////

bool is_trivial_copy_type(Type const *type)
{
  return type->flags & Type::TrivialCopy;
}

bool is_trivial_assign_type(Type const *type)
{
  return type->flags & Type::TrivialAssign;
}

bool is_trivial_destroy_type(Type const *type)
{
  return type->flags & Type::TrivialDestroy;
}

bool is_literal_copy_type(Type const *type)
{
  return (type->flags & Type::TrivialCopy) || (type->flags & Type::LiteralCopy);
}

//|///////////////////// remove_const_type //////////////////////////////////
Type const *remove_const_type(Type const *type)
{
  if (type->klass() == Type::Const)
    type = type_cast<ConstType>(type)->type;

  if (type->klass() == Type::QualArg)
    type = type_cast<QualArgType>(type)->type;

  return type;
}

Type *remove_const_type(Type *type)
{
  if (type->klass() == Type::Const)
    type = type_cast<ConstType>(type)->type;

  if (type->klass() == Type::QualArg)
    type = type_cast<QualArgType>(type)->type;

  return type;
}

//|///////////////////// remove_pointer_type ////////////////////////////////
Type const *remove_pointer_type(Type const *type)
{
  if (type->klass() == Type::Pointer)
    type = type_cast<PointerType>(type)->type;

  return type;
}

Type *remove_pointer_type(Type *type)
{
  if (type->klass() == Type::Pointer)
    type = type_cast<PointerType>(type)->type;

  return type;
}

//|///////////////////// is_voidpointer_type ////////////////////////////////
bool is_voidpointer_type(Type const *type)
{
  return is_pointference_type(type) && is_void_type(remove_qualifiers_type(type));
}

//|///////////////////// is_pointference_type ///////////////////////////////
bool is_pointference_type(Type const *type)
{
  return is_pointer_type(type) || is_reference_type(type);
}

//|///////////////////// remove_reference_type //////////////////////////////
Type const *remove_reference_type(Type const *type)
{
  if (type->klass() == Type::Reference)
    type = type_cast<ReferenceType>(type)->type;

  return type;
}

Type *remove_reference_type(Type *type)
{
  if (type->klass() == Type::Reference)
    type = type_cast<ReferenceType>(type)->type;

  return type;
}

//|///////////////////// remove_pointference_type //////////////////////////////
Type const *remove_pointference_type(Type const *type)
{
  if (type->klass() == Type::Pointer)
    type = type_cast<PointerType>(type)->type;
  else if (type->klass() == Type::Reference)
    type = type_cast<ReferenceType>(type)->type;

  return type;
}

Type *remove_pointference_type(Type *type)
{
  if (type->klass() == Type::Pointer)
    type = type_cast<PointerType>(type)->type;
  else if (type->klass() == Type::Reference)
    type = type_cast<ReferenceType>(type)->type;

  return type;
}

//|///////////////////// remove_qualifiers_type /////////////////////////////
Type const *remove_qualifiers_type(Type const *type)
{
  type = remove_const_type(type);

  while (is_pointer_type(type) || is_reference_type(type))
    type = remove_const_type(remove_pointference_type(type));

  return type;
}

Type *remove_qualifiers_type(Type *type)
{
  type = remove_const_type(type);

  while (is_pointer_type(type) || is_reference_type(type))
    type = remove_const_type(remove_pointference_type(type));

  return type;
}

//|///////////////////// print //////////////////////////////////////////////
std::ostream &operator <<(std::ostream &os, Type const &type)
{
  switch (type.klass())
  {
    case Type::Builtin:
      os << *static_cast<BuiltinType const &>(type).name();
      break;

    case Type::Const:
      os << *static_cast<ConstType const &>(type).type << " const";
      break;

    case Type::Pointer:
      switch (auto ptr = static_cast<PointerType const &>(type).type; ptr->klass())
      {
        case Type::Const:
          os << *static_cast<ConstType const *>(ptr)->type << " *";
          break;

        default:
          os << *ptr << " mut *";
          break;
      }
      break;

    case Type::Reference:
      switch (auto ref = static_cast<ReferenceType const &>(type).type; ref->klass())
      {
        case Type::Const:
          os << *static_cast<ConstType const *>(ref)->type << " &";
          break;

        case Type::QualArg:
          os << *ref << " &&";
          break;

        default:
          os << *ref << " mut &";
          break;
      }
      break;

    case Type::Slice:
      os << *static_cast<SliceType const &>(type).type << " [*]";
      break;

    case Type::Array:
      os << *static_cast<ArrayType const &>(type).type << " [" << *static_cast<ArrayType const &>(type).size << "]";
      break;

    case Type::Tuple:
      if (auto &tuple = static_cast<TupleType const &>(type); true)
      {
        os << '(';

        int i = 0;
        for (auto &field : tuple.fields)
          os << (!i++ ? "" : ", ") << *field;

        os << ')';
      }
      break;

    case Type::Tag:
      if (auto &tag = static_cast<TagType const &>(type); true)
      {
        os << *tag.decl;

        if (any_of(tag.args.begin(), tag.args.end(), [](auto arg) { return !is_typearg_type(arg.second) || type_cast<TypeArgType>(arg.second)->decl != arg.first; }))
        {
          os << '<';

          int i = 0;
          for (auto &[decl, type] : tag.args)
            os << (!i++ ? "" : ", ") << *decl << ": " << *type;

          os << '>';
        }
      }
      break;

    case Type::TypeRef:
      os << *static_cast<TypeRefType const &>(type).decl;
      break;

    case Type::TypeArg:
      if (auto &arg = static_cast<TypeArgType const &>(type); true)
      {
        if (arg.koncept)
          os << *arg.koncept;
        else
          os << *arg.decl;
      }
      break;

    case Type::QualArg:
      if (auto qual = static_cast<QualArgType const &>(type); qual.type)
      {
        os << *qual.type;

        if (qual.qualifiers & QualArgType::Const)
          os << " const";

        if (qual.qualifiers & QualArgType::RValue)
          os << " rvalue";
      }
      break;

    case Type::TypeLit:
      os << *static_cast<TypeLitType const &>(type).value;
      break;

    case Type::Constant:
      if (auto &constant = static_cast<ConstantType const &>(type); true)
      {
        os << *get<Decl*>(constant.decl->owner) << "::" << *constant.decl;
      }
      break;

    case Type::Function:
      if (auto &fn = static_cast<FunctionType const &>(type); true)
      {
        os << "fn " << *fn.paramtuple;

        if (fn.throwtype != Builtin::type(Builtin::Type_Void))
          os << " throws(" << *fn.throwtype << ")";

        os << " -> " << *fn.returntype;
      }
      break;

    case Type::Pack:
      os << *static_cast<PackType const &>(type).type << " ...";
      break;

    case Type::Unpack:
      os << *static_cast<UnpackType const &>(type).type << "...";
      break;
  }

  return os;
}


//|--------------------- Type -----------------------------------------------
//|--------------------------------------------------------------------------

//|///////////////////// Type::Constructor //////////////////////////////////
Type::Type(Klass klass)
  : m_klass(klass)
{
}


//|--------------------- BuiltinType ----------------------------------------
//|--------------------------------------------------------------------------

//|///////////////////// BuiltinType::Constructor ///////////////////////////
BuiltinType::BuiltinType(Kind kind)
  : Type(Builtin),
    m_kind(kind)
{
  if (!(m_kind == IntLiteral || m_kind == FloatLiteral || m_kind == DeclidLiteral || m_kind == TypeidLiteral))
    flags |= Type::Concrete;

  if (m_kind == IntLiteral || m_kind == FloatLiteral || m_kind == PtrLiteral || m_kind == DeclidLiteral || m_kind == TypeidLiteral)
    flags |= Type::Indefinite;

  if (sizeof_type(this) == 0)
    flags |= Type::ZeroSized;

  flags |= Type::TrivialCopy;
  flags |= Type::TrivialAssign;
  flags |= Type::TrivialDestroy;
}

//|///////////////////// is-literal_valid ///////////////////////////////////
bool is_literal_valid(BuiltinType::Kind kind, Numeric::Int const &value)
{
  if (value.overflowed)
    return false;

  switch (kind)
  {
    case BuiltinType::Bool:
      return (value.sign > 0 && value.value <= 1);

    case BuiltinType::I8:
      return (value.sign < 0 && value.value <= uint64_t(std::numeric_limits<int8_t>::max())+1) || (value.sign > 0 && value.value <= uint64_t(std::numeric_limits<int8_t>::max()));

    case BuiltinType::I16:
      return (value.sign < 0 && value.value <= uint64_t(std::numeric_limits<int16_t>::max())+1) || (value.sign > 0 && value.value <= uint64_t(std::numeric_limits<int16_t>::max()));

    case BuiltinType::I32:
      return (value.sign < 0 && value.value <= uint64_t(std::numeric_limits<int32_t>::max())+1) || (value.sign > 0 && value.value <= uint64_t(std::numeric_limits<int32_t>::max()));

    case BuiltinType::I64:
    case BuiltinType::ISize:
      return (value.sign < 0 && value.value <= uint64_t(std::numeric_limits<int64_t>::max())+1) || (value.sign > 0 && value.value <= uint64_t(std::numeric_limits<int64_t>::max()));

    case BuiltinType::U8:
      return (value.sign > 0 && value.value <= uint64_t(std::numeric_limits<uint8_t>::max())) || (value.maybe_unsigned && value.value - 1 <= uint64_t(std::numeric_limits<uint8_t>::max()));

    case BuiltinType::U16:
      return (value.sign > 0 && value.value <= uint64_t(std::numeric_limits<uint16_t>::max())) || (value.maybe_unsigned && value.value - 1 <= uint64_t(std::numeric_limits<uint16_t>::max()));;

    case BuiltinType::U32:
    case BuiltinType::Char:
      return (value.sign > 0 && value.value <= uint64_t(std::numeric_limits<uint32_t>::max())) || (value.maybe_unsigned && value.value - 1 <= uint64_t(std::numeric_limits<uint32_t>::max()));;

    case BuiltinType::U64:
    case BuiltinType::USize:
      return (value.sign > 0 && value.value <= uint64_t(std::numeric_limits<uint64_t>::max())) || (value.maybe_unsigned && value.value - 1<= uint64_t(std::numeric_limits<uint64_t>::max()));;

    case BuiltinType::IntLiteral:
    case BuiltinType::DeclidLiteral:
    case BuiltinType::TypeidLiteral:
      return true;

    default:
      assert(false);
  }

  return false;
}

//|///////////////////// is_literal_valid ///////////////////////////////////
bool is_literal_valid(BuiltinType::Kind kind, Numeric::Float const &value)
{
  if (value.overflowed)
    return false;

  switch (kind)
  {
    case BuiltinType::F32:
      return true;

    case BuiltinType::F64:
      return true;

    case BuiltinType::FloatLiteral:
      return true;

    default:
      assert(false);
  }

  return false;
}

//|///////////////////// BuiltinType::dump /////////////////////////////////
void BuiltinType::dump(int indent) const
{
  cout << spaces(indent) << "BuiltinType " << this << " #" << name() << '\n';
}


//|--------------------- ConstType ------------------------------------------
//|--------------------------------------------------------------------------

//|///////////////////// ConstType::Constructor /////////////////////////////
ConstType::ConstType(Type *type)
  : Type(Const),
    type(type)
{
  flags |= type->flags & Type::Concrete;
  flags |= type->flags & Type::Indefinite;
  flags |= type->flags & Type::Unresolved;
  flags |= type->flags & Type::ZeroSized;
  flags |= type->flags & Type::TrivialCopy;
  flags |= type->flags & Type::TrivialAssign;
  flags |= type->flags & Type::TrivialDestroy;
  flags |= type->flags & Type::LiteralCopy;
}

//|///////////////////// ConstType::dump ////////////////////////////////////
void ConstType::dump(int indent) const
{
  cout << spaces(indent) << "ConstType " << this << '\n';

  if (type)
  {
    type->dump(indent + 2);
  }
}


//|--------------------- PointerType ----------------------------------------
//|--------------------------------------------------------------------------

//|///////////////////// PointerType::Constructor ///////////////////////////
PointerType::PointerType(Type *type)
  : Type(Pointer),
    type(type)
{
  flags |= type->flags & Type::Concrete;
  flags |= type->flags & Type::Indefinite;
  flags |= type->flags & Type::Unresolved;
  flags |= Type::TrivialCopy;
  flags |= Type::TrivialAssign;
  flags |= Type::TrivialDestroy;
}

//|///////////////////// PointerType::dump //////////////////////////////////
void PointerType::dump(int indent) const
{
  cout << spaces(indent) << "PointerType " << this << '\n';

  if (type)
  {
    type->dump(indent + 2);
  }
}


//|--------------------- ReferenceType --------------------------------------
//|--------------------------------------------------------------------------

//|///////////////////// ReferenceType::Constructor /////////////////////////
ReferenceType::ReferenceType(Type *type)
  : Type(Reference),
    type(type)
{
  flags |= type->flags & Type::Concrete;
  flags |= type->flags & Type::Indefinite;
  flags |= type->flags & Type::Unresolved;
  flags |= Type::TrivialCopy;
  flags |= Type::TrivialDestroy;

  if (is_function_type(remove_qualifiers_type(type)))
    flags |= Type::TrivialAssign;
}

//|///////////////////// ReferenceType::dump ////////////////////////////////
void ReferenceType::dump(int indent) const
{
  cout << spaces(indent) << "ReferenceType " << this << '\n';

  if (type)
  {
    type->dump(indent + 2);
  }
}


//|--------------------- SliceType ------------------------------------------
//|--------------------------------------------------------------------------

//|///////////////////// SliceType::Constructor /////////////////////////////
SliceType::SliceType(Type *type)
  : Type(Slice),
    type(type)
{
  flags |= Type::TrivialCopy;
  flags |= Type::TrivialAssign;
  flags |= Type::TrivialDestroy;
  flags |= type->flags & Type::Concrete;
  flags |= type->flags & Type::Indefinite;
  flags |= type->flags & Type::Unresolved;
}

//|///////////////////// SliceType::dump ////////////////////////////////////
void SliceType::dump(int indent) const
{
  cout << spaces(indent) << "SliceType " << this << '\n';

  if (type)
  {
    type->dump(indent + 2);
  }
}


//|--------------------- ArrayType ------------------------------------------
//|--------------------------------------------------------------------------

//|///////////////////// ArrayType::Constructor /////////////////////////////
ArrayType::ArrayType(Type *type, Type *size)
  : Type(Array),
    type(type),
    size(size)
{
  flags |= type->flags & Type::ZeroSized;
  flags |= type->flags & Type::TrivialCopy;
  flags |= type->flags & Type::TrivialAssign;
  flags |= type->flags & Type::TrivialDestroy;
  flags |= type->flags & Type::LiteralCopy;

  if (size->klass() == Type::TypeLit && type_cast<TypeLitType>(size)->value->kind() == Expr::IntLiteral)
  {
    flags |= type->flags & Type::Concrete;
    flags |= type->flags & Type::Indefinite;
    flags |= type->flags & Type::Unresolved;

    if (expr_cast<IntLiteralExpr>(type_cast<TypeLitType>(size)->value)->value().value == 0)
    {
      flags |= Type::ZeroSized;
      flags |= Type::TrivialCopy;
      flags |= Type::TrivialAssign;
      flags |= Type::TrivialDestroy;
      flags |= Type::LiteralCopy;
    }

    if (expr_cast<IntLiteralExpr>(type_cast<TypeLitType>(size)->value)->value().value > 0x7fffffffffffffff)
      flags |= Type::Unresolved;
  }

  if (size->klass() != Type::TypeLit || type_cast<TypeLitType>(size)->value->kind() != Expr::IntLiteral)
    flags |= Type::Unresolved;
}

//|///////////////////// ArrayType::dump ////////////////////////////////////
void ArrayType::dump(int indent) const
{
  cout << spaces(indent) << "ArrayType " << this << '\n';

  if (type)
  {
    type->dump(indent + 2);
  }

  if (size)
  {
    size->dump(indent + 2);
  }
}

//|///////////////////// array_len //////////////////////////////////////////
size_t array_len(ArrayType const *type)
{
  return expr_cast<IntLiteralExpr>(type_cast<TypeLitType>(type->size)->value)->value().value;
}


//|--------------------- CompoundType ---------------------------------------
//|--------------------------------------------------------------------------

//|///////////////////// CompoundType::Constructor //////////////////////////
CompoundType::CompoundType(Klass klass)
  : Type(klass)
{
}

//|///////////////////// CompoundType::Constructor //////////////////////////
CompoundType::CompoundType(Klass klass, vector<Type*> &&resolved_fields)
  : Type(klass),
    fields(std::move(resolved_fields))
{
}


//|--------------------- TupleType ------------------------------------------
//|--------------------------------------------------------------------------

//|///////////////////// TupleType::Constructor /////////////////////////////
TupleType::TupleType(vector<Type*> const &fields)
  : CompoundType(Tuple, vector<Type*>(fields))
{
  flags |= Type::Unresolved;
}

TupleType::TupleType(vector<Type*> &&resolved_defns, vector<Type*> &&resolved_fields)
  : CompoundType(Tuple, std::move(resolved_fields)),
    defns(std::move(resolved_defns))
{
  if (all_of(fields.begin(), fields.end(), [](auto k) { return is_concrete_type(k); }))
    flags |= Type::Concrete;

  if (any_of(fields.begin(), fields.end(), [](auto k) { return is_indefinite_type(k); }))
    flags |= Type::Indefinite;

  if (any_of(fields.begin(), fields.end(), [](auto k) { return is_unresolved_type(k); }))
    flags |= Type::Unresolved;

  if (all_of(fields.begin(), fields.end(), [](auto k) { return (k->flags & Type::ZeroSized); }))
    flags |= Type::ZeroSized;

  if (all_of(fields.begin(), fields.end(), [](auto k) { return (k->flags & Type::TrivialCopy); }))
    flags |= Type::TrivialCopy;

  if (all_of(fields.begin(), fields.end(), [](auto k) { return (k->flags & Type::TrivialAssign); }))
    flags |= Type::TrivialAssign;

  if (all_of(fields.begin(), fields.end(), [](auto k) { return (k->flags & Type::TrivialDestroy); }))
    flags |= Type::TrivialDestroy;

  if (all_of(fields.begin(), fields.end(), [](auto k) { return (k->flags & Type::LiteralCopy); }))
    flags |= Type::LiteralCopy;
}

//|///////////////////// TupleType::dump ////////////////////////////////////
void TupleType::dump(int indent) const
{
  cout << spaces(indent) << "TupleType " << this << " '" << *this << "'\n";
}

//|///////////////////// tuple_len //////////////////////////////////////////
size_t tuple_len(TupleType const *type)
{
  return type->fields.size();
}


//|--------------------- TypeArgType ----------------------------------------
//|--------------------------------------------------------------------------

//|///////////////////// TypeArgType::Constructor ///////////////////////////
TypeArgType::TypeArgType(Decl *decl)
  : Type(TypeArg),
    decl(decl)
{
  flags |= Type::Indefinite;
  flags |= Type::Unresolved;
}

TypeArgType::TypeArgType(Decl *decl, Decl *koncept, vector<pair<Decl*, Type*>> const &args)
  : Type(TypeArg),
    decl(decl),
    koncept(koncept),
    args(args)
{
  flags |= Type::Indefinite;
  flags |= Type::Unresolved;
}

//|///////////////////// TypeArgType::dump //////////////////////////////////
void TypeArgType::dump(int indent) const
{
  cout << spaces(indent) << "TypeArgType " << this << " '" << *this << "'\n";

  if (koncept)
  {
    koncept->dump(indent + 2);
  }
}


//|--------------------- QualArgType ----------------------------------------
//|--------------------------------------------------------------------------

//|///////////////////// QualArgType::Constructor ///////////////////////////
QualArgType::QualArgType(Type *type, long qualifiers)
  : Type(QualArg),
    qualifiers(qualifiers),
    type(type)
{
  flags |= type->flags & Type::Concrete;
  flags |= type->flags & Type::Indefinite;
  flags |= type->flags & Type::Unresolved;
  flags |= type->flags & Type::ZeroSized;
  flags |= type->flags & Type::TrivialCopy;
  flags |= type->flags & Type::TrivialAssign;
  flags |= type->flags & Type::TrivialDestroy;
  flags |= type->flags & Type::LiteralCopy;
}

//|///////////////////// QualArgType::dump //////////////////////////////////
void QualArgType::dump(int indent) const
{
  cout << spaces(indent) << "QualArgType " << this << '\n';

  if (type)
  {
    type->dump(indent + 2);
  }
}


//|--------------------- TypeLitType ----------------------------------------
//|--------------------------------------------------------------------------

//|///////////////////// TypeLitType::Constructor ///////////////////////////
TypeLitType::TypeLitType(Expr *value)
  : Type(TypeLit),
    value(value)
{
  flags |= Type::ZeroSized;
}

//|///////////////////// TypeLitType::dump //////////////////////////////////
void TypeLitType::dump(int indent) const
{
  cout << spaces(indent) << "TypeLitType " << this << " '" << *this << "'\n";
}


//|///////////////////// TypeLitType::equals ////////////////////////////////

bool equals(Expr *lhs, Expr *rhs)
{
  if (lhs->kind() != rhs->kind())
    return false;

  switch (lhs->kind())
  {
    case Expr::VoidLiteral:
      return true;

    case Expr::BoolLiteral:
      return expr_cast<BoolLiteralExpr>(lhs)->value() == expr_cast<BoolLiteralExpr>(rhs)->value();

    case Expr::CharLiteral:
      return expr_cast<CharLiteralExpr>(lhs)->value() == expr_cast<CharLiteralExpr>(rhs)->value();

    case Expr::IntLiteral:
      return expr_cast<IntLiteralExpr>(lhs)->value() == expr_cast<IntLiteralExpr>(rhs)->value();

    case Expr::FloatLiteral:
      return expr_cast<FloatLiteralExpr>(lhs)->value() == expr_cast<FloatLiteralExpr>(rhs)->value();

    case Expr::StringLiteral:
      return expr_cast<StringLiteralExpr>(lhs)->value() == expr_cast<StringLiteralExpr>(rhs)->value();

    case Expr::PointerLiteral:
      return true;

    case Expr::FunctionPointer:
      return expr_cast<FunctionPointerExpr>(lhs)->value() == expr_cast<FunctionPointerExpr>(rhs)->value();

    case Expr::ArrayLiteral:

      if (expr_cast<ArrayLiteralExpr>(lhs)->elements.size() != expr_cast<ArrayLiteralExpr>(rhs)->elements.size())
        return false;

      if (!equals(type_cast<TypeLitType>(expr_cast<ArrayLiteralExpr>(lhs)->size)->value, type_cast<TypeLitType>(expr_cast<ArrayLiteralExpr>(rhs)->size)->value))
        return false;

      for (size_t i = 0; i < expr_cast<ArrayLiteralExpr>(lhs)->elements.size(); ++i)
      {
        if (!equals(expr_cast<ArrayLiteralExpr>(lhs)->elements[i], expr_cast<ArrayLiteralExpr>(rhs)->elements[i]))
          return false;
      }

      return true;

    case Expr::CompoundLiteral:

      if (expr_cast<CompoundLiteralExpr>(lhs)->fields.size() != expr_cast<CompoundLiteralExpr>(rhs)->fields.size())
        return false;

      for (size_t i = 0; i < expr_cast<CompoundLiteralExpr>(lhs)->fields.size(); ++i)
      {
        if (!equals(expr_cast<CompoundLiteralExpr>(lhs)->fields[i], expr_cast<CompoundLiteralExpr>(rhs)->fields[i]))
          return false;
      }

      return true;

    default:
      assert(false);
  }

  return false;
}

bool equals(TypeLitType *lhs, Expr *rhs)
{
  return equals(lhs->value, rhs);
}

bool equals(TypeLitType *lhs, TypeLitType *rhs)
{
  return equals(lhs->value, rhs->value);
}


//|--------------------- ConstantType ---------------------------------------
//|--------------------------------------------------------------------------

//|///////////////////// ConstantType::Constructor //////////////////////////
ConstantType::ConstantType(Decl *decl, Type *type)
  : Type(Constant),
    decl(decl),
    type(type)
{
  flags |= Type::Unresolved;
}

//|///////////////////// ConstantType::resolve //////////////////////////////
void ConstantType::resolve(Type *resolved_expr)
{
  flags &= ~Type::Unresolved;

  expr = resolved_expr;
}

//|///////////////////// ConstantType::dump /////////////////////////////////
void ConstantType::dump(int indent) const
{
  cout << spaces(indent) << "ConstantType " << this << " '" << *this << "'\n";
}


//|--------------------- TypeRefType ----------------------------------------
//|--------------------------------------------------------------------------

//|///////////////////// TypeRefType::Constructor ///////////////////////////
TypeRefType::TypeRefType(Decl *decl)
  : Type(TypeRef),
    decl(decl)
{
  flags |= Type::Unresolved;
}

//|///////////////////// TypeRefType::dump //////////////////////////////////
void TypeRefType::dump(int indent) const
{
  cout << spaces(indent) << "TypeRefType " << this << " '" << *this << "'\n";
}


//|--------------------- TagType --------------------------------------------
//|--------------------------------------------------------------------------

//|///////////////////// TagType::Constructor ///////////////////////////////
TagType::TagType(Decl *decl, vector<pair<Decl*, Type*>> const &args)
  : CompoundType(Tag),
    decl(decl),
    args(args)
{
  flags |= Type::Unresolved;
  flags |= Type::Incomplete;

  if (decl->flags & TagDecl::Packed)
    flags |= Type::Packed;
}

//|///////////////////// TagType::resolve ///////////////////////////////////
void TagType::resolve(vector<Decl*> &&resolved_decls)
{
  flags |= Type::Concrete;
  flags &= ~Type::Unresolved;

  decls = std::move(resolved_decls);
}

//|///////////////////// TagType::resolve ///////////////////////////////////
void TagType::resolve(vector<Type*> &&resolved_fields)
{
  fields = std::move(resolved_fields);

  if (decl->kind() == Decl::Struct || decl->kind() == Decl::Union || decl->kind() == Decl::VTable || decl->kind() == Decl::Lambda)
  {
    flags &= ~Type::Concrete;

    if (all_of(fields.begin(), fields.end(), [](auto k) { return is_concrete_type(k); }))
      flags |= Type::Concrete;

    if (any_of(fields.begin(), fields.end(), [](auto k) { return is_indefinite_type(k); }))
      flags |= Type::Indefinite;

    if (any_of(fields.begin(), fields.end(), [](auto k) { return is_unresolved_type(k); }))
      flags |= Type::Unresolved;

    if (all_of(fields.begin(), fields.end(), [](auto k) { return (k->flags & Type::ZeroSized); }))
      flags |= Type::ZeroSized;
  }

  if (decl->kind() == Decl::Enum)
  {
    flags |= Type::Concrete;
    flags |= Type::TrivialCopy;
    flags |= Type::TrivialAssign;
    flags |= Type::TrivialDestroy;
  }

  for (auto &decl : decls)
  {
    if (decl->kind() == Decl::FieldVar)
    {
      fieldvars.push_back(decl);
    }

    if (decl->kind() == Decl::Function)
    {
      auto fn = decl_cast<FunctionDecl>(decl);

      if ((fn->flags & FunctionDecl::Defaulted) && (fn->builtin == Builtin::Default_Copytructor))
      {
        if (all_of(fields.begin(), fields.end(), [](auto k) { return (k->flags & Type::TrivialCopy); }))
          flags |= Type::TrivialCopy;
      }

      if ((fn->flags & FunctionDecl::Defaulted) && (fn->builtin == Builtin::Default_Assignment))
      {
        if (all_of(fields.begin(), fields.end(), [](auto k) { return (k->flags & Type::TrivialAssign); }))
          flags |= Type::TrivialAssign;
      }

      if ((fn->flags & FunctionDecl::Defaulted) && (fn->builtin == Builtin::Default_Destructor))
      {
        if (all_of(fields.begin(), fields.end(), [](auto k) { return (k->flags & Type::TrivialDestroy); }))
          flags |= Type::TrivialDestroy;
      }

      if ((fn->flags & FunctionDecl::Defaulted) && (fn->builtin == Builtin::Literal_Copytructor))
      {
        flags |= Type::LiteralCopy;
      }
    }
  }

  flags &= ~Type::Incomplete;
}

//|///////////////////// TagType::dump //////////////////////////////////////
void TagType::dump(int indent) const
{
  cout << spaces(indent) << "TagType " << this << " '" << *this << "'\n";
}


//|--------------------- FunctionType ---------------------------------------
//|--------------------------------------------------------------------------

//|///////////////////// FunctionType::Constructor //////////////////////////
FunctionType::FunctionType(Type *returntype, Type *paramtuple, Type *throwtype)
  : Type(Function),
    returntype(returntype),
    paramtuple(paramtuple),
    throwtype(throwtype)
{
  flags |= (returntype->flags & Type::Concrete) & (paramtuple->flags & Type::Concrete);
  flags |= (returntype->flags & Type::Unresolved) | (paramtuple->flags & Type::Unresolved);
}


//|///////////////////// FunctionType::dump /////////////////////////////////
void FunctionType::dump(int indent) const
{
  cout << spaces(indent) << "FunctionType " << this << " '" << *this << "'\n";
}


//|--------------------- PackType -------------------------------------------
//|--------------------------------------------------------------------------

//|///////////////////// PackType::Constructor //////////////////////////////
PackType::PackType(Type *type)
  : Type(Pack),
    type(type)
{
}

//|///////////////////// PackType::dump /////////////////////////////////////
void PackType::dump(int indent) const
{
  cout << spaces(indent) << "PackType " << this << '\n';

  if (type)
  {
    type->dump(indent + 2);
  }
}


//|--------------------- UnpackType -----------------------------------------
//|--------------------------------------------------------------------------

//|///////////////////// UnpackType::Constructor ////////////////////////////
UnpackType::UnpackType(Type *type)
  : Type(Unpack),
    type(type)
{
}

//|///////////////////// UnpackType::dump ///////////////////////////////////
void UnpackType::dump(int indent) const
{
  cout << spaces(indent) << "UnpackType " << this << '\n';

  if (type)
  {
    type->dump(indent + 2);
  }
}


//|--------------------- Size & Alignment -----------------------------------
//|--------------------------------------------------------------------------

//|///////////////////// sizeof_array ///////////////////////////////////////
size_t sizeof_type(ArrayType const *type)
{
  return sizeof_type(type->type) * array_len(type);
}

//|///////////////////// sizeof_struct //////////////////////////////////////
size_t sizeof_type(TagType const *type)
{
  size_t size = 0;
  size_t align = 1;

  if (is_union_type(type))
  {
    if (type->fields.empty())
      return 0;

    auto tagsize = sizeof_type(type->fields[0]);

    for (size_t i = 1; i < type->fields.size(); ++i)
    {
      size = max(size, sizeof_type(type->fields[i]));
      align = max(align, alignof_type(type->fields[i]));
    }

    size = ((tagsize + align - 1) & -align) + size;
    align = max(align, alignof_type(type->fields[0]));
  }
  else
  {
    for (auto &field : type->fields)
    {
      if (!(type->flags & Type::Packed))
      {
        auto alignment = alignof_type(field);

        size = (size + alignment - 1) & -alignment;

        align = max(align, alignment);
      }

      size += sizeof_type(field);
    }
  }

  if (auto alignment = decl_cast<TagDecl>(type->decl)->alignment; alignment != 0)
  {
    align = max(align, alignment);
  }

  return (size + align - 1) & -align;
}

//|///////////////////// sizeof_tuple ///////////////////////////////////////
size_t sizeof_type(TupleType const *type)
{
  size_t size = 0;
  size_t align = 1;

  for (auto &field : type->fields)
  {
    auto alignment = alignof_type(field);

    size = ((size + alignment - 1) & -alignment) + sizeof_type(field);

    align = max(align, alignment);
  }

  return (size + align - 1) & -align;
}

//|///////////////////// sizeof_type ////////////////////////////////////////
size_t sizeof_type(Type const *type)
{
  assert(type);

  switch (type->klass())
  {
    case Type::Builtin:
      switch (type_cast<BuiltinType>(type)->kind())
      {
        case BuiltinType::Void:
          return 0;
        case BuiltinType::Bool:
          return 1;
        case BuiltinType::Char:
          return 4;
        case BuiltinType::I8:
          return 1;
        case BuiltinType::I16:
          return 2;
        case BuiltinType::I32:
          return 4;
        case BuiltinType::I64:
          return 8;
        case BuiltinType::ISize:
          return 8;
        case BuiltinType::U8:
          return 1;
        case BuiltinType::U16:
          return 2;
        case BuiltinType::U32:
          return 4;
        case BuiltinType::U64:
          return 8;
        case BuiltinType::USize:
          return 8;
        case BuiltinType::F32:
          return 4;
        case BuiltinType::F64:
          return 8;

        case BuiltinType::PtrLiteral:
          return sizeof(void*);

        case BuiltinType::StringLiteral:
          return 8 + sizeof(void*);

        case BuiltinType::IntLiteral:
        case BuiltinType::DeclidLiteral:
        case BuiltinType::TypeidLiteral:
          return sizeof(Numeric::Int);

        case BuiltinType::FloatLiteral:
          return sizeof(Numeric::Float);
      }
      break;

    case Type::Const:
      return sizeof_type(type_cast<ConstType>(type)->type);

    case Type::QualArg:
      return sizeof_type(type_cast<QualArgType>(type)->type);

    case Type::Pointer:
    case Type::Reference:
      return sizeof(void*);

    case Type::Slice:
      return 8 + sizeof(void*);

    case Type::Array:
      return sizeof_type(type_cast<ArrayType>(type));

    case Type::Tuple:
      return sizeof_type(type_cast<TupleType>(type));

    case Type::Tag:
      return sizeof_type(type_cast<TagType>(type));

    case Type::TypeLit:
      return 0;

    case Type::Function:
      return 0;

    default:
      assert(false);
  }

  throw logic_error("invalid type for size");
}

//|///////////////////// alignof_struct /////////////////////////////////////
size_t alignof_type(TagType const *type)
{
  size_t align = 1;

  if (!(type->flags & Type::Packed))
  {
    for (auto &field : type->fields)
    {
      align = max(align, alignof_type(field));
    }
  }

  if (auto alignment = decl_cast<TagDecl>(type->decl)->alignment; alignment != 0)
  {
    align = max(align, alignment);
  }

  return align;
}

//|///////////////////// alignof_tuple //////////////////////////////////////
size_t alignof_type(TupleType const *type)
{
  size_t align = 1;

  for (auto &field : type->fields)
  {
    align = max(align, alignof_type(field));
  }

  return align;
}

//|///////////////////// alignof_type ///////////////////////////////////////
size_t alignof_type(Type const *type)
{
  assert(type);

  switch (type->klass())
  {
    case Type::Builtin:
      switch (type_cast<BuiltinType>(type)->kind())
      {
        case BuiltinType::Bool:
          return 1;
        case BuiltinType::Char:
          return 4;
        case BuiltinType::I8:
          return 1;
        case BuiltinType::I16:
          return 2;
        case BuiltinType::I32:
          return 4;
        case BuiltinType::I64:
          return 8;
        case BuiltinType::ISize:
          return 8;
        case BuiltinType::U8:
          return 1;
        case BuiltinType::U16:
          return 2;
        case BuiltinType::U32:
          return 4;
        case BuiltinType::U64:
          return 8;
        case BuiltinType::USize:
          return 8;
        case BuiltinType::F32:
          return 4;
        case BuiltinType::F64:
          return 8;

        case BuiltinType::Void:
          return 1;

        case BuiltinType::PtrLiteral:
          return 8;

        case BuiltinType::StringLiteral:
          return 8;

        case BuiltinType::IntLiteral:
        case BuiltinType::DeclidLiteral:
        case BuiltinType::TypeidLiteral:
          return alignof(Numeric::Int);

        case BuiltinType::FloatLiteral:
          return alignof(Numeric::Float);
      }
      break;

    case Type::Const:
      return alignof_type(type_cast<ConstType>(type)->type);

    case Type::QualArg:
      return alignof_type(type_cast<QualArgType>(type)->type);

    case Type::Pointer:
    case Type::Reference:
      return alignof(void*);

    case Type::Slice:
      return alignof(void*);

    case Type::Array:
      return alignof_type(type_cast<ArrayType>(type)->type);

    case Type::Tuple:
      return alignof_type(type_cast<TupleType>(type));

    case Type::Tag:
      return alignof_type(type_cast<TagType>(type));

    case Type::TypeLit:
      return 1;

    case Type::Function:
      return 1;

    default:
      assert(false);
  }

  throw logic_error("invalid type for align");
}

//|///////////////////// sizeof_field ///////////////////////////////////////
size_t sizeof_field(CompoundType const *type, size_t index)
{
  return sizeof_type(type->fields[index]);
}

//|///////////////////// alignof_field //////////////////////////////////////
size_t alignof_field(CompoundType const *type, size_t index)
{
  return alignof_type(type->fields[index]);
}

//|///////////////////// offsetof_field /////////////////////////////////////
size_t offsetof_field(CompoundType const *type, size_t index)
{
  size_t offset = 0;

  if (is_union_type(type))
  {
     if (index != 0)
     {
       auto alignment = alignof_type(type);

       offset = (sizeof_field(type, 0) + alignment - 1) & -alignment;
     }

     return offset;
  }

  if (is_compound_type(type))
  {
    for (auto &field : type->fields)
    {
      if (!(type->flags & Type::Packed))
      {
        auto alignment = alignof_field(type, &field - &type->fields[0]);

        offset = (offset + alignment - 1) & -alignment;
      }

      if (index == 0)
        break;

      offset += sizeof_type(field);

      index -= 1;
    }

    return offset;
  }

  return 0;
}
