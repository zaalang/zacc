//
// lower.h
//
// Copyright (c) 2020-2023 Peter Niekamp. All rights reserved.
//
// This file is part of zaalang, which is BSD-2-Clause licensed.
// See http://opensource.org/licenses/BSD-2-Clause
//

#pragma once

#include "ast.h"
#include "mir.h"
#include "query.h"
#include <functional>

//-------------------------- TypeTable --------------------------------------
//---------------------------------------------------------------------------

struct TypeTable
{
  std::unordered_map<Type*, ConstType*> const_types;
  std::unordered_map<Type*, PointerType*> pointer_types;
  std::unordered_map<Type*, ReferenceType*> reference_types;
  std::unordered_map<Type*, SliceType*> slice_types;
  std::unordered_multimap<Type*, ArrayType*> array_types;
  std::unordered_multimap<Type*, TupleType*> tuple_types;
  std::unordered_multimap<Decl*, TagType*> tag_types;
  std::unordered_multimap<Decl*, ConstantType*> constant_types;
  std::vector<FunctionType*> fn_types;
  std::vector<QualArgType*> qualarg_types;
  std::vector<TypeLitType*> int_literal_types;
  std::vector<TypeLitType*> string_literal_types;
  std::vector<TypeLitType*> other_literal_types;

  Type *var_defn = make_type<TypeArgType>(new TypeArgDecl({}));
  TupleType *empty_tuple = make_type<TupleType>(std::vector<Type*>{}, std::vector<Type*>{});

  std::map<std::tuple<Decl*, std::vector<std::pair<Decl*, Type*>>, Type*>, std::tuple<std::vector<std::pair<Decl*, Type*>>, Type*, bool>> concepts;

  std::unordered_map<FnSig, Expr*> injections;

  template<typename T>
  T *find_or_create(Type *subtype);

  template<typename T>
  T *find(Decl *decl, std::vector<std::pair<Decl*, Type*>> const &args);

  template<typename T>
  T *create(Decl *decl, std::vector<std::pair<Decl*, Type*>> const &args);

  template<typename T>
  T *find_or_create(Type *elemtype, Type *sizetype);

  template<typename T>
  T *find_or_create(std::vector<Type*> &&defns, std::vector<Type*> &&fields);

  template<typename T>
  T *find_or_create(long qualifiers, Type *subtype);

  template<typename T>
  T *find_or_create(Type *returntype, Type *paramtuple, Type *throwtype);

  template<typename T>
  T *find_or_create(Expr *expr);

  template<typename T>
  T *find(Decl *decl, Type *type);

  template<typename T>
  T *create(Decl *decl, Type *type);

  template<typename T, typename ...Args>
  T *make_type(Args&&... args);

  template<typename T, typename ...Args>
  T *make_expr(Args&&... args);
};

template<>
inline ConstType *TypeTable::find_or_create<ConstType>(Type *subtype)
{
  auto j = const_types.find(subtype);

  if (j == const_types.end())
  {
    j = const_types.emplace(subtype, make_type<ConstType>(subtype)).first;
  }

  return j->second;
}

template<>
inline PointerType *TypeTable::find_or_create<PointerType>(Type *subtype)
{
  auto j = pointer_types.find(subtype);

  if (j == pointer_types.end())
  {
    j = pointer_types.emplace(subtype, make_type<PointerType>(subtype)).first;
  }

  return j->second;
}

template<>
inline ReferenceType *TypeTable::find_or_create<ReferenceType>(Type *subtype)
{
  auto j = reference_types.find(subtype);

  if (j == reference_types.end())
  {
    j = reference_types.emplace(subtype, make_type<ReferenceType>(subtype)).first;
  }

  return j->second;
}

template<>
inline SliceType *TypeTable::find_or_create<SliceType>(Type *elemtype)
{
  auto j = slice_types.find(elemtype);

  if (j == slice_types.end())
  {
    j = slice_types.emplace(elemtype, make_type<SliceType>(elemtype)).first;
  }

  return j->second;
}

template<>
inline ArrayType *TypeTable::find_or_create<ArrayType>(Type *elemtype, Type *sizetype)
{
  auto range = array_types.equal_range(elemtype);

  auto j = find_if(range.first, range.second, [&](auto &k) { return k.second->size == sizetype; });

  if (j == range.second)
  {
    j = array_types.emplace(elemtype, make_type<ArrayType>(elemtype, sizetype));
  }

  return j->second;
}

template<>
inline TupleType *TypeTable::find_or_create<TupleType>(std::vector<Type*> &&defns, std::vector<Type*> &&fields)
{
  if (fields.empty())
    return empty_tuple;

  auto key = fields[0];
  auto range = tuple_types.equal_range(key);

  auto j = find_if(range.first, range.second, [&](auto &k) { return k.second->defns == defns && k.second->fields == fields; });

  if (j == range.second)
  {
    j = tuple_types.emplace(key, make_type<TupleType>(std::move(defns), std::move(fields)));
  }

  return j->second;
}

template<>
inline TagType *TypeTable::find<TagType>(Decl *decl, std::vector<std::pair<Decl*, Type*>> const &args)
{
  auto range = tag_types.equal_range(decl);

  auto j = find_if(range.first, range.second, [&](auto &k) { return k.second->args == args; });

  if (j == range.second)
    return nullptr;

  return j->second;
}

template<>
inline TagType *TypeTable::create<TagType>(Decl *decl, std::vector<std::pair<Decl*, Type*>> const &args)
{
  return tag_types.emplace(decl, make_type<TagType>(decl, args))->second;
}

template<>
inline FunctionType *TypeTable::find_or_create<FunctionType>(Type *returntype, Type *paramtuple, Type *throwtype)
{
  auto j = find_if(fn_types.begin(), fn_types.end(), [&](auto &k) { return k->returntype == returntype && k->paramtuple == paramtuple && k->throwtype == throwtype; });

  if (j == fn_types.end())
  {
    j = fn_types.emplace(fn_types.end(), make_type<FunctionType>(returntype, paramtuple, throwtype));
  }

  return *j;
}

template<>
inline QualArgType *TypeTable::find_or_create<QualArgType>(long qualifiers, Type *subtype)
{
  auto j = find_if(qualarg_types.begin(), qualarg_types.end(), [&](auto &k) { return k->qualifiers == qualifiers && k->type == subtype; });

  if (j == qualarg_types.end())
  {
    j = qualarg_types.emplace(qualarg_types.end(), make_type<QualArgType>(subtype, qualifiers));
  }

  return *j;
}

template<>
inline TypeLitType *TypeTable::find_or_create<TypeLitType>(Expr *expr)
{
  switch (expr->kind())
  {
    case Expr::IntLiteral:

      for (auto &lit : int_literal_types)
      {
        if (expr_cast<IntLiteralExpr>(lit->value)->value() == expr_cast<IntLiteralExpr>(expr)->value())
          return lit;
      }

      int_literal_types.push_back(make_type<TypeLitType>(make_expr<IntLiteralExpr>(expr_cast<IntLiteralExpr>(expr)->value(), expr->loc())));

      return int_literal_types.back();

    case Expr::StringLiteral:

      for (auto &lit : string_literal_types)
      {
        if (expr_cast<StringLiteralExpr>(lit->value)->value() == expr_cast<StringLiteralExpr>(expr)->value())
          return lit;
      }

      string_literal_types.push_back(make_type<TypeLitType>(make_expr<StringLiteralExpr>(expr_cast<StringLiteralExpr>(expr)->value(), expr->loc())));

      return string_literal_types.back();

    case Expr::VoidLiteral:
    case Expr::BoolLiteral:
    case Expr::CharLiteral:
    case Expr::FloatLiteral:
    case Expr::PointerLiteral:
    case Expr::FunctionPointer:
    case Expr::ArrayLiteral:
    case Expr::CompoundLiteral:

      for (auto &lit : other_literal_types)
      {
        if (equals(lit, expr))
          return lit;
      }

      switch (expr->kind())
      {
        case Expr::VoidLiteral:
          other_literal_types.push_back(make_type<TypeLitType>(make_expr<VoidLiteralExpr>(expr->loc())));
          break;

        case Expr::BoolLiteral:
          other_literal_types.push_back(make_type<TypeLitType>(make_expr<BoolLiteralExpr>(expr_cast<BoolLiteralExpr>(expr)->value(), expr->loc())));
          break;

        case Expr::CharLiteral:
          other_literal_types.push_back(make_type<TypeLitType>(make_expr<CharLiteralExpr>(expr_cast<CharLiteralExpr>(expr)->value(), expr->loc())));
          break;

        case Expr::FloatLiteral:
          other_literal_types.push_back(make_type<TypeLitType>(make_expr<FloatLiteralExpr>(expr_cast<FloatLiteralExpr>(expr)->value(), expr->loc())));
          break;

        case Expr::PointerLiteral:
          other_literal_types.push_back(make_type<TypeLitType>(make_expr<PointerLiteralExpr>(expr->loc())));
          break;

        case Expr::FunctionPointer:
          other_literal_types.push_back(make_type<TypeLitType>(make_expr<FunctionPointerExpr>(expr_cast<FunctionPointerExpr>(expr)->value(), expr->loc())));
          break;

        case Expr::ArrayLiteral: {

          std::vector<Expr*> elements;

          for (auto &element : expr_cast<ArrayLiteralExpr>(expr)->elements)
            elements.push_back(find_or_create<TypeLitType>(element)->value);

          other_literal_types.push_back(make_type<TypeLitType>(make_expr<ArrayLiteralExpr>(elements, expr_cast<ArrayLiteralExpr>(expr)->size, expr->loc())));

          break;
        }

        case Expr::CompoundLiteral: {

          std::vector<Expr*> fields;

          for (auto &field : expr_cast<CompoundLiteralExpr>(expr)->fields)
            fields.push_back(find_or_create<TypeLitType>(field)->value);

          other_literal_types.push_back(make_type<TypeLitType>(make_expr<CompoundLiteralExpr>(fields, expr->loc())));

          break;
        }

        default:
          assert(false);
      }

      return other_literal_types.back();

    default:
      assert(false);
  }

  throw std::logic_error("unresolved literal type");
}

template<>
inline ConstantType *TypeTable::find<ConstantType>(Decl *decl, Type *type)
{
  auto range = constant_types.equal_range(decl);

  auto j = find_if(range.first, range.second, [&](auto &k) { return k.second->type == type; });

  if (j == range.second)
    return nullptr;

  return j->second;
}

template<>
inline ConstantType *TypeTable::create<ConstantType>(Decl *decl, Type *type)
{
  return constant_types.emplace(decl, make_type<ConstantType>(decl, type))->second;
}

template<typename T, typename ...Args>
T *TypeTable::make_type(Args&&... args)
{
  return new T(std::forward<Args>(args)...);
}

template<typename T, typename ...Args>
T *TypeTable::make_expr(Args&&... args)
{
  return new T(std::forward<Args>(args)...);
}

//-------------------------- Lower ------------------------------------------
//---------------------------------------------------------------------------

namespace LowerFlags
{
  enum LowerFlags
  {
  };
}

MIR const &lower(FnSig const &fx, TypeTable &typetable, class Diag &diag);
MIR lower(Scope const &scope, Expr *expr, std::unordered_map<Decl*, MIR::Fragment> const &symbols, TypeTable &typetable, class Diag &diag);
MIR lower(FnSig const &fx, TypeTable &typetable, class Diag &diag, long flags);
