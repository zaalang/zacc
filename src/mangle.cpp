//
// mangle.cpp
//
// Copyright (C) 2020 Peter Niekamp. All rights reserved.
//
// This file is part of zaalang, which is BSD-2-Clause licensed.
// See http://opensource.org/licenses/BSD-2-Clause
//

#include "mangle.h"
#include "decl.h"
#include "stmt.h"
#include "expr.h"
#include "type.h"
#include <cassert>

using namespace std;

namespace
{
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

    // add parameter types (just v for none to distinguish functions from types)
    result += 'v';

    return result;
  }

  //|///////////////////// function_parameters //////////////////////////////
  string function_parameters(FunctionDecl const *fn)
  {
    string result;

    // return type
    if (!(fn->flags & FunctionDecl::Destructor))
      result += "v";

    result += "v";

    return result;
  }

  //|///////////////////// mangle_scope /////////////////////////////////////
  string mangle_scope(Decl *decl)
  {
    switch (decl->kind())
    {
      case Decl::Module:
      {
        auto name = decl_cast<ModuleDecl>(decl)->name;

        if (isdigit(name[0]))
          name.insert(0, "_");

        return mangle_name(name);
      }

      case Decl::Function:
      {
        auto fn = decl_cast<FunctionDecl>(decl);

        return mangle_scope(fn->owner) + mangle_name(fn->name + "I" + type_parameters(fn) + "EE" + function_parameters(fn));
      }

      case Decl::Struct:
      case Decl::Lambda:
      case Decl::Concept:
      case Decl::Enum:
      {
        auto strct = decl_cast<TagDecl>(decl);

        return mangle_scope(strct->owner) + mangle_name(strct->name);
      }

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

            for(auto &stmt : stmt_cast<CompoundStmt>(owner)->stmts)
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

      case Stmt::Declaration:
        return mangle_scope(stmt->owner);

      default:
        throw logic_error("invalid stmt for mangling");
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
  if (fn->flags & FunctionDecl::ExternC)
  {
    return fn->name;
  }

  return "_ZN" + mangle_scope(fn->owner) + mangle_name(fn->name) + "I" + type_parameters(fn) + "EE" + function_parameters(fn);
}
