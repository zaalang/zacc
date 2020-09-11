//
// type.cpp
//
// Copyright (C) 2020 Peter Niekamp. All rights reserved.
//
// This file is part of zaalang, which is BSD-2-Clause licensed.
// See http://opensource.org/licenses/BSD-2-Clause
//

#include "ast.h"
#include <iostream>
#include <climits>
#include <cassert>

using namespace std;

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
      for(int i = 0; i < indent.n; ++i)
        os << ' ';

      return os;
    }

    int n;
  };
}

//|///////////////////// is_void_type ///////////////////////////////////////
bool is_void_type(Type const *type)
{
  return (type->klass() == Type::Builtin && type_cast<BuiltinType>(type)->is_void_type());
}

//|///////////////////// is_int_type ////////////////////////////////////////
bool is_int_type(Type const *type)
{
  return (type->klass() == Type::Builtin && type_cast<BuiltinType>(type)->is_int_type());
}

//|///////////////////// is_float_type /////////////////////////////////////
bool is_float_type(Type const *type)
{
  return (type->klass() == Type::Builtin && type_cast<BuiltinType>(type)->is_float_type());
}

//|///////////////////// is_char_type ///////////////////////////////////////
bool is_char_type(Type const *type)
{
  return (type->klass() == Type::Builtin && type_cast<BuiltinType>(type)->is_char_type());
}

//|///////////////////// is_string_type /////////////////////////////////////
bool is_string_type(Type const *type)
{
  return (type->klass() == Type::Builtin && type_cast<BuiltinType>(type)->kind() == BuiltinType::StringLiteral);
}

//|///////////////////// is_bool_type ///////////////////////////////////////
bool is_bool_type(Type const *type)
{
  return (type->klass() == Type::Builtin && type_cast<BuiltinType>(type)->is_bool_type());
}

//|///////////////////// is_signed_type /////////////////////////////////////
bool is_signed_type(Type const *type)
{
  return (type->klass() == Type::Builtin && type_cast<BuiltinType>(type)->is_signed_type());
}

//|///////////////////// is_const_type //////////////////////////////////////
bool is_const_type(Type const *type)
{
  return (type->klass() == Type::Const);
}

//|///////////////////// is_builtin_type ////////////////////////////////////
bool is_builtin_type(Type const *type)
{
  return (type->klass() == Type::Builtin);
}

//|///////////////////// is_pointer_type ////////////////////////////////////
bool is_pointer_type(Type const *type)
{
  return (type->klass() == Type::Pointer);
}

//|///////////////////// is_reference_type //////////////////////////////////
bool is_reference_type(Type const *type)
{
  return (type->klass() == Type::Reference);
}

//|///////////////////// is_typearg_type ////////////////////////////////////
bool is_typearg_type(Type const *type)
{
  return (type->klass() == Type::TypeArg);
}

//|///////////////////// is_qualarg_type ////////////////////////////////////
bool is_qualarg_type(Type const *type)
{
  return (type->klass() == Type::QualArg);
}

//|///////////////////// is_typelit_type ////////////////////////////////////
bool is_typelit_type(Type const *type)
{
  return (type->klass() == Type::TypeLit);
}

//|///////////////////// is_array_type //////////////////////////////////////
bool is_array_type(Type const *type)
{
  return (type->klass() == Type::Array);
}

//|///////////////////// is_tuple_type //////////////////////////////////////
bool is_tuple_type(Type const *type)
{
  return (type->klass() == Type::Tuple);
}

//|///////////////////// is_function_type ///////////////////////////////////
bool is_function_type(Type const *type)
{
  return (type->klass() == Type::Function);
}

//|///////////////////// is_pack_type ///////////////////////////////////////
bool is_pack_type(Type const *type)
{
  return (type->klass() == Type::Pack);
}

//|///////////////////// is_unpack_type /////////////////////////////////////
bool is_unpack_type(Type const *type)
{
  return (type->klass() == Type::Unpack);
}

//|///////////////////// is_tag_type ////////////////////////////////////////
bool is_tag_type(Type const *type)
{
  return (type->klass() == Type::Tag);
}

//|///////////////////// is_struct_type /////////////////////////////////////
bool is_struct_type(Type const *type)
{
  return (is_tag_type(type) && type_cast<TagType>(type)->decl->kind() == Decl::Struct);
}

//|///////////////////// is_lambda_type /////////////////////////////////////
bool is_lambda_type(Type const *type)
{
  return (is_tag_type(type) && type_cast<TagType>(type)->decl->kind() == Decl::Lambda);
}

//|///////////////////// is_enum_type ///////////////////////////////////////
bool is_enum_type(Type const *type)
{
  return (is_tag_type(type) && type_cast<TagType>(type)->decl->kind() == Decl::Enum);
}

//|///////////////////// is_compound_type ///////////////////////////////////
bool is_compound_type(Type const *type)
{
  return is_tuple_type(type) || is_struct_type(type) || is_lambda_type(type);
}

//|///////////////////// is_concrete_type ///////////////////////////////////
bool is_concrete_type(Type const *type)
{
  switch (type->klass())
  {
    case Type::Const:
      return is_concrete_type(type_cast<ConstType>(type)->type);

    case Type::Pointer:
      return is_concrete_type(type_cast<PointerType>(type)->type);

    case Type::Reference:
      return is_concrete_type(type_cast<ReferenceType>(type)->type);

    case Type::QualArg:
      return is_concrete_type(type_cast<QualArgType>(type)->type);

    default:
      return type->flags & Type::Concrete;
  }
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

//|///////////////////// print //////////////////////////////////////////////
std::ostream &operator <<(std::ostream &os, Type const &type)
{
  switch (type.klass())
  {
    case Type::Builtin:
      os << static_cast<BuiltinType const &>(type).name();
      break;

    case Type::Const:
      os << *static_cast<ConstType const &>(type).type << " const";
      break;

    case Type::Pointer:
      os << *static_cast<PointerType const &>(type).type << " *";
      break;

    case Type::Reference: {
      os << *static_cast<ReferenceType const &>(type).type << " &";
      if (is_qualarg_type(static_cast<ReferenceType const &>(type).type))
        os << '&';
      break;
    }

    case Type::Array:
      os << *static_cast<ArrayType const &>(type).type << " [" << *static_cast<ArrayType const &>(type).size << "]";
      break;

    case Type::Tuple:
      if (auto &tuple = static_cast<TupleType const &>(type); true)
      {
        os << '(';

        int i = 0;
        for(auto &field : tuple.fields)
          os << (!i++ ? "" : ", ") << *field;

        os << ')';
      }
      break;

    case Type::Tag:
      if (auto &tag = static_cast<TagType const &>(type); true)
      {
        os << *tag.decl;

        if (tag.args.size() != 0)
        {
          os << '<';

          int i = 0;
          for(auto &[decl, type] : tag.args)
            os << (!i++ ? "" : ", ") << *decl << ": " << *type;

          os << '>';
        }
      }
      break;

    case Type::TypeRef:
      os << *static_cast<TypeRefType const &>(type).decl;
      break;

    case Type::TypeArg:
      os << *static_cast<TypeArgType const &>(type).decl;
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
        os << *fn.returntype << *fn.paramtuple;
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
  flags |= Type::TrivialCopy;
  flags |= Type::TrivialAssign;
  flags |= Type::TrivialDestroy;

  if (is_concrete_type())
    flags |= Type::Concrete;

  if (sizeof_type(this) == 0)
    flags |= Type::ZeroSized;
}


//|///////////////////// BuiltinType::name //////////////////////////////////
const char *BuiltinType::name() const
{
  switch (m_kind)
  {
    case Void: return "void";
    case Bool: return "bool";
    case Char: return "char";
    case I8: return "i8";
    case I16: return "i16";
    case I32: return "i32";
    case I64: return "i64";
    case ISize: return "isize";
    case U8: return "u8";
    case U16: return "u16";
    case U32: return "u32";
    case U64: return "u64";
    case USize: return "usize";
    case F32: return "f32";
    case F64: return "f64";
    case IntLiteral: return "#int";
    case FloatLiteral: return "#float";
    case StringLiteral: return "#string";
    case PtrLiteral: return "null";
  }

  throw logic_error("invalid builtin type");
}

//|///////////////////// literal_valid //////////////////////////////////////
bool literal_valid(BuiltinType::Kind kind, Numeric::Int const &value)
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
      return (value.sign > 0 && value.value <= uint64_t(std::numeric_limits<uint8_t>::max()));

    case BuiltinType::U16:
      return (value.sign > 0 && value.value <= uint64_t(std::numeric_limits<uint16_t>::max()));

    case BuiltinType::U32:
    case BuiltinType::Char:
      return (value.sign > 0 && value.value <= uint64_t(std::numeric_limits<uint32_t>::max()));

    case BuiltinType::U64:
    case BuiltinType::USize:
      return (value.sign > 0 && value.value <= uint64_t(std::numeric_limits<uint64_t>::max()));

    case BuiltinType::IntLiteral:
      return true;

    default:
      assert(false);
  }

  return false;
}

//|///////////////////// literal_valid //////////////////////////////////////
bool literal_valid(BuiltinType::Kind kind, Numeric::Float const &value)
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
  flags |= type->flags & Type::ZeroSized;
  flags |= type->flags & Type::TrivialCopy;
  flags |= type->flags & Type::TrivialAssign;
  flags |= type->flags & Type::TrivialDestroy;
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
  flags |= Type::Concrete;
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
  flags |= Type::Concrete;
  flags |= Type::TrivialCopy;
  flags |= Type::TrivialDestroy;
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

  if (size->klass() == Type::TypeLit && type_cast<TypeLitType>(size)->value->kind() == Expr::IntLiteral)
  {
    flags |= type->flags & Type::Concrete;

    if (expr_cast<IntLiteralExpr>(type_cast<TypeLitType>(size)->value)->value().value == 0)
    {
      flags |= Type::ZeroSized;
      flags |= Type::TrivialCopy;
      flags |= Type::TrivialAssign;
      flags |= Type::TrivialDestroy;
    }
  }
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
CompoundType::CompoundType(Klass klass, vector<Type*> const &fields)
  : Type(klass),
    fields(fields)
{
}


//|--------------------- TupleType ------------------------------------------
//|--------------------------------------------------------------------------

//|///////////////////// TupleType::Constructor /////////////////////////////
TupleType::TupleType(vector<Type*> const &defns, vector<Type*> const &fields)
  : CompoundType(Tuple, fields),
    defns(defns)
{
  if (all_of(fields.begin(), fields.end(), [](auto k) { return is_concrete_type(k); }))
    flags |= Type::Concrete;

  if (all_of(fields.begin(), fields.end(), [](auto k) { return (k->flags & Type::ZeroSized); }))
    flags |= Type::ZeroSized;

  if (all_of(fields.begin(), fields.end(), [](auto k) { return (k->flags & Type::TrivialCopy); }))
    flags |= Type::TrivialCopy;

  if (all_of(fields.begin(), fields.end(), [](auto k) { return (k->flags & Type::TrivialAssign); }))
    flags |= Type::TrivialAssign;

  if (all_of(fields.begin(), fields.end(), [](auto k) { return (k->flags & Type::TrivialDestroy); }))
    flags |= Type::TrivialDestroy;
}

TupleType::TupleType(vector<Type*> const &fields)
  : CompoundType(Tuple, fields)
{
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
}

TypeArgType::TypeArgType(Decl *decl, Decl *koncept, vector<pair<Decl*, Type*>> const &args)
  : Type(TypeArg),
    decl(decl),
    koncept(koncept),
    args(args)
{
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
  flags |= type->flags & Type::ZeroSized;
  flags |= type->flags & Type::TrivialCopy;
  flags |= type->flags & Type::TrivialAssign;
  flags |= type->flags & Type::TrivialDestroy;
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

  switch(lhs->kind())
  {
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

    case Expr::ArrayLiteral:

      if (expr_cast<ArrayLiteralExpr>(lhs)->elements.size() != expr_cast<ArrayLiteralExpr>(rhs)->elements.size())
        return false;

      if (!equals(type_cast<TypeLitType>(expr_cast<ArrayLiteralExpr>(lhs)->size)->value, type_cast<TypeLitType>(expr_cast<ArrayLiteralExpr>(rhs)->size)->value))
        return false;

      for(size_t i = 0; i < expr_cast<ArrayLiteralExpr>(lhs)->elements.size(); ++i)
      {
        if (!equals(expr_cast<ArrayLiteralExpr>(lhs)->elements[i], expr_cast<ArrayLiteralExpr>(rhs)->elements[i]))
          return false;
      }

      return true;

    case Expr::CompoundLiteral:

      if (expr_cast<CompoundLiteralExpr>(lhs)->fields.size() != expr_cast<CompoundLiteralExpr>(rhs)->fields.size())
        return false;

      for(size_t i = 0; i < expr_cast<CompoundLiteralExpr>(lhs)->fields.size(); ++i)
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
}

//|///////////////////// ConstantType::resolve //////////////////////////////
void ConstantType::resolve(Type *resolved_expr)
{
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
  flags |= Type::Concrete; // assume concrete until resolvle (for self ref)
}

//|///////////////////// TagType::resolve ///////////////////////////////////
void TagType::resolve(vector<Decl*> &&resolved_decls, vector<Type*> &&resolved_fields)
{
  // Maybe we should resolve all the subtypes in this pass so that pointers/references/consts can update
  // their concrete (and others?) flags appropriately. The above concrete assumption could be resolved.
  // For now pointers/references don't abide their concrete flags, just pass along the subtype.

  decls = std::move(resolved_decls);
  fields = std::move(resolved_fields);

  if (decl->kind() == Decl::Struct || decl->kind() == Decl::Lambda)
  {
    if (any_of(fields.begin(), fields.end(), [](auto k) { return !is_concrete_type(k); }))
      flags &= ~Type::Concrete;

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

  for(auto &decl : decls)
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
    }
  }
}

//|///////////////////// TagType::dump //////////////////////////////////////
void TagType::dump(int indent) const
{
  cout << spaces(indent) << "TagType " << this << " '" << *this << "'\n";
}


//|--------------------- FunctionType ---------------------------------------
//|--------------------------------------------------------------------------

//|///////////////////// FunctionType::Constructor //////////////////////////
FunctionType::FunctionType(Type *returntype, Type *paramtuple)
  : Type(Function),
    returntype(returntype),
    paramtuple(paramtuple)
{
  if (is_concrete_type(returntype) && is_concrete_type(paramtuple))
    flags |= Type::Concrete;
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

  for(auto &field : type->fields)
  {
    auto alignment = alignof_type(field);

    size = ((size + alignment - 1) & -alignment) + sizeof_type(field);

    align = max(align, alignment);
  }

  return ((size + align - 1) & -align);
}

//|///////////////////// sizeof_tuple ///////////////////////////////////////
size_t sizeof_type(TupleType const *type)
{
  size_t size = 0;
  size_t align = 1;

  for(auto &field : type->fields)
  {
    auto alignment = alignof_type(field);

    size = ((size + alignment - 1) & -alignment) + sizeof_type(field);

    align = max(align, alignment);
  }

  return ((size + align - 1) & -align);
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
          return 0;

        case BuiltinType::StringLiteral:
          return 8 + sizeof(void*);

        case BuiltinType::IntLiteral:
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

    case Type::Array:
      return sizeof_type(type_cast<ArrayType>(type));

    case Type::Tuple:
      return sizeof_type(type_cast<TupleType>(type));

    case Type::Tag:
      return sizeof_type(type_cast<TagType>(type));

    default:
      assert(false);
  }

  throw logic_error("invalid type for size");
}

//|///////////////////// alignof_struct /////////////////////////////////////
size_t alignof_type(TagType const *type)
{
  size_t align = 1;

  for(auto &field : type->fields)
  {
    align = max(align, alignof_type(field));
  }

  return align;
}

//|///////////////////// alignof_tuple //////////////////////////////////////
size_t alignof_type(TupleType const *type)
{
  size_t align = 1;

  for(auto &field : type->fields)
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
          return 0;

        case BuiltinType::StringLiteral:
          return 8;

        case BuiltinType::IntLiteral:
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

    case Type::Array:
      return alignof_type(type_cast<ArrayType>(type)->type);

    case Type::Tuple:
      return alignof_type(type_cast<TupleType>(type));

    case Type::Tag:
      return alignof_type(type_cast<TagType>(type));

    default:
      assert(false);
  }

  throw logic_error("invalid type for align");
}

//|///////////////////// offsetof_type //////////////////////////////////////
size_t offsetof_type(Type const *type, size_t index)
{
  assert(type);

  type = remove_const_type(type);

  if (is_compound_type(type))
  {
    size_t offset = 0;

    for(auto &field : type_cast<CompoundType>(type)->fields)
    {
      auto alignment = alignof_type(field);

      offset = (offset + alignment - 1) & -alignment;

      if (index == 0)
        break;

      offset += sizeof_type(field);

      index -= 1;
    }

    return offset;
  }

  if (is_array_type(type))
  {
    auto arraytype = type_cast<ArrayType>(type);

    return index * sizeof_type(arraytype->type);
  }

  throw logic_error("invalid type for offset");
}
