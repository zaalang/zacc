//
// mangle.cpp
//
// Copyright (c) 2020-2023 Peter Niekamp. All rights reserved.
//
// This file is part of zaalang, which is BSD-2-Clause licensed.
// See http://opensource.org/licenses/BSD-2-Clause
//

#include "mangle.h"
#include "ident.h"
#include "decl.h"
#include "stmt.h"
#include "expr.h"
#include "type.h"
#include <cassert>

using namespace std;

namespace
{
  //|///////////////////// mangle_type //////////////////////////////////////
  void mangle_type(string &name, Type const *type)
  {
    switch (type->klass())
    {
      case Type::Builtin:
        switch (type_cast<BuiltinType>(type)->kind())
        {
          case BuiltinType::Void:
            name += 'v';
            break;

          case BuiltinType::Bool:
            name += 'b';
            break;

          case BuiltinType::Char:
            name += "Di";
            break;

          case BuiltinType::I8:
            name += 'a';
            break;

          case BuiltinType::I16:
            name += 's';
            break;

          case BuiltinType::I32:
            name += 'i';
            break;

          case BuiltinType::I64:
            name += 'x';
            break;

          case BuiltinType::ISize:
            name += 'x';
            break;

          case BuiltinType::U8:
            name += 'h';
            break;

          case BuiltinType::U16:
            name += 't';
            break;

          case BuiltinType::U32:
            name += 'j';
            break;

          case BuiltinType::U64:
            name += 'y';
            break;

          case BuiltinType::USize:
            name += 'y';
            break;

          case BuiltinType::F32:
            name += 'f';
            break;

          case BuiltinType::F64:
            name += 'd';
            break;

          case BuiltinType::StringLiteral:
          case BuiltinType::IntLiteral:
          case BuiltinType::FloatLiteral:
          case BuiltinType::DeclidLiteral:
          case BuiltinType::TypeidLiteral:
          case BuiltinType::PtrLiteral:
            name += "Da";
            break;
        }
        break;

      case Type::Const:
        name += 'K';
        mangle_type(name, type_cast<ConstType>(type)->type);
        break;

      case Type::QualArg:
        mangle_type(name, type_cast<QualArgType>(type)->type);
        break;

      case Type::Pointer:
        name += 'P';
        mangle_type(name, type_cast<PointerType>(type)->type);
        break;

      case Type::Reference:
        name += 'R';
        mangle_type(name, type_cast<ReferenceType>(type)->type);
        break;

      case Type::Array:
        name += 'A';
        name += '_';
        mangle_type(name, type_cast<ArrayType>(type)->type);
        break;

      case Type::Tuple:
      case Type::Tag:
      case Type::Function:
      case Type::TypeArg:
      case Type::TypeRef:
      case Type::Pack:
        name += "Da";
        break;

      default:
        assert(false);
    }
  }

  //|///////////////////// mangle_name //////////////////////////////////////
  string mangle_name(string_view name)
  {
    if (name == "~") return "co";
    if (name == "+") return "pl";
    if (name == "-") return "mi";
    if (name == "*") return "ml";
    if (name == "/") return "dv";
    if (name == "%") return "rm";
    if (name == "&") return "an";
    if (name == "|") return "or";
    if (name == "^") return "eo";
    if (name == "=") return "aS";
    if (name == "+=") return "pL";
    if (name == "-=") return "mI";
    if (name == "*=") return "mL";
    if (name == "/=") return "dV";
    if (name == "%=") return "rM";
    if (name == "&=") return "aN";
    if (name == "|=") return "oR";
    if (name == "^=") return "eO";
    if (name == "<<") return "ls";
    if (name == ">>") return "rs";
    if (name == "<<=") return "lS";
    if (name == ">>=") return "rS";
    if (name == "==") return "eq";
    if (name == "!=") return "ne";
    if (name == "<") return "lt";
    if (name == ">") return "gt";
    if (name == "<=") return "le";
    if (name == ">=") return "ge";
    if (name == "<=>") return "ss";
    if (name == "~=") return "5matchD0";
    if (name == "!") return "nt";
    if (name == "&&") return "aa";
    if (name == "||") return "oo";
    if (name == "++") return "pp";
    if (name == "--") return "mm";
    if (name == "->") return "pt";
    if (name == "()") return "cl";
    if (name == "[]") return "ix";

    if (name == "~#array") return "5arrayD0";
    if (name == "~#tuple") return "5tupleD0";
    if (name == "~#lambda") return "6lambdaD0";
    if (name == "~#vtable") return "6vtableD0";
    if (name == "#builtin") return "St7builtin";

    if (name.front() == '~') return "D0";
    if (name.front() == '#') return to_string(name.size()-1) + string(name.begin()+1, name.end());
    if (name.back() == '=') return to_string(name.size()-1) + string(name.begin(), name.end()-1) + "eq";

    return to_string(name.size()) + string(name);
  }

  //|///////////////////// type_parameters //////////////////////////////////
  string type_parameters(FunctionDecl const *fn)
  {
    string result;

    for (auto parm : fn->args)
    {
      (void)parm;
      result += "Da";
    }

    return result;
  }

  //|///////////////////// function_parameters //////////////////////////////
  string function_parameters(FunctionDecl const *fn)
  {
    string result;

    if (!(fn->flags & FunctionDecl::Destructor))
    {
      if (fn->returntype)
        mangle_type(result, fn->returntype);
      else
        result += 'v';
    }

    for (auto parm : fn->parms)
    {
      mangle_type(result, decl_cast<ParmVarDecl>(parm)->type);
    }

    if (fn->parms.empty())
      result += "v";

    return result;
  }

  //|///////////////////// mangle_scope /////////////////////////////////////
  string mangle_scope(Decl *decl)
  {
    switch (decl->kind())
    {
      case Decl::Module: {
        auto module = decl_cast<ModuleDecl>(decl);

        if (isdigit(module->name->sv()[0]))
          return mangle_name("_" + module->name->str());

        return mangle_name(module->name->sv());
      }

      case Decl::Function: {
        auto fn = decl_cast<FunctionDecl>(decl);

        if (!fn->name)
          return mangle_scope(fn->owner);

        return mangle_scope(fn->owner) + mangle_name(fn->name->sv());
      }

      case Decl::Struct:
      case Decl::Union:
      case Decl::VTable:
      case Decl::Lambda:
      case Decl::Concept:
      case Decl::Enum: {
        auto strct = decl_cast<TagDecl>(decl);

        if (!strct->name)
          return mangle_scope(strct->owner) + "9anonymous";

        return mangle_scope(strct->owner) + mangle_name(strct->name->sv());
      }

      case Decl::Case:
      case Decl::TypeAlias:
        return mangle_scope(decl->owner);

      default:
        throw logic_error("invalid decl for mangling");
    }
  }

  //|///////////////////// mangle_scope /////////////////////////////////////
  string mangle_scope(Stmt *stmt)
  {
    switch (stmt->kind())
    {
      case Stmt::Compound:
      {
        auto compound = stmt_cast<CompoundStmt>(stmt);

        auto scope = mangle_scope(compound->owner);

        if (holds_alternative<Stmt*>(compound->owner))
        {
          auto owner = get<Stmt*>(compound->owner);

          if (owner->kind() == Stmt::Compound)
          {
            int count = 0;

            for (auto &stmt : stmt_cast<CompoundStmt>(owner)->stmts)
            {
              if (stmt == owner)
                break;

              if (stmt->kind() == Stmt::Compound)
                ++count;
            }

            scope += mangle_name("_" + to_string(count));
          }
        }

        return scope;
      }

      default:
        return mangle_scope(stmt->owner);
    }
  }
}

//|///////////////////// mangle_scope /////////////////////////////////////
string mangle_scope(variant<Decl*, Stmt*> const &scope)
{
  return std::visit([&](auto &v) { return mangle_scope(v); }, scope);
}

//|///////////////////// get_mangled_name /////////////////////////////////
string get_mangled_name(FunctionDecl const *fn)
{
  if (fn->flags & FunctionDecl::ExternMask)
    return fn->name->str();

  return "_ZN" + mangle_scope(fn->owner) + mangle_name(fn->name->str()) + "I" + type_parameters(fn) + "EE" + function_parameters(fn);
}

//|///////////////////// get_mangled_name /////////////////////////////////
string get_mangled_name(FunctionDecl const *fn, std::string_view name)
{
  return "_ZZ" + mangle_scope(fn->owner) + mangle_name(fn->name->str()) + "I" + type_parameters(fn) + "EE" + mangle_name(name);
}
