//
// query.h
//
// Copyright (C) 2020 Peter Niekamp. All rights reserved.
//
// This file is part of zaalang, which is BSD-2-Clause licensed.
// See http://opensource.org/licenses/BSD-2-Clause
//

#pragma once

#include "ast.h"
#include <string>
#include <string_view>
#include <variant>

namespace QueryFlags
{
  enum QueryFlags
  {
    Modules = 0x1,   // include module decls
    Functions = 0x2, // include function decls
    Variables = 0x4, // include variable decls
    Types = 0x8,     // include type decls
    Fields = 0x10,   // include field decls
    Concepts = 0x20, // include concept decls
    Imports = 0x40,  // include import decls
    Usings = 0x80,   // include using decls

    All = 0x7FFF,

    Public = 0x8000  // exclude non public decls
  };
}

struct Scope
{
  Stmt const *goalpost = nullptr;

  std::variant<Decl*, Stmt*> owner;
  std::vector<std::pair<Decl*, Type*>> typeargs;

  void set_type(Decl *in, Type *out);

  auto find_type(Decl *decl)
  {
    return std::find_if(typeargs.begin(), typeargs.end(), [&](auto &k) { return k.first == decl; });
  }

  auto find_type(Decl *decl) const
  {
    return std::find_if(typeargs.begin(), typeargs.end(), [&](auto &k) { return k.first == decl; });
  }

  friend bool operator ==(Scope const &lhs, Scope const &rhs)
  {
    return lhs.owner == rhs.owner && lhs.goalpost == rhs.goalpost && lhs.typeargs == rhs.typeargs;
  }

  friend bool operator !=(Scope const &lhs, Scope const &rhs)
  {
    return !(lhs == rhs);
  }

  bool operator!() const { return owner == std::variant<Decl*, Stmt*>(); }
  explicit operator bool() const { return owner != std::variant<Decl*, Stmt*>(); }

  Scope() = default;
  Scope(Decl *owner) : owner(owner) { }
  Scope(Stmt *owner) : owner(owner) { }
  Scope(Decl *owner, std::vector<std::pair<Decl*, Type*>> typeargs) : owner(owner), typeargs(std::move(typeargs)) { }
  Scope(Stmt *owner, std::vector<std::pair<Decl*, Type*>> typeargs) : owner(owner), typeargs(std::move(typeargs)) { }
};

bool is_fn_scope(Scope const &scope);
bool is_tag_scope(Scope const &scope);
bool is_stmt_scope(Scope const &scope);
bool is_module_scope(Scope const &scope);

void seed_stack(std::vector<Scope> &stack, Scope scope);

Scope parent_scope(Scope scope);
Scope super_scope(Scope scope, std::variant<Decl*, Stmt*> const &owner);
Scope child_scope(Scope scope, std::variant<Decl*, Stmt*> const &owner, std::vector<std::pair<Decl*, Type*>> const &typeargs = {});

ModuleDecl *get_module(Scope const &scope);

void find_decl(Decl *decl, std::string_view name, long flags, std::vector<Decl*> &results);
void find_decls(Scope const &scope, std::string_view name, long flags, std::vector<Decl*> &results);

std::ostream &operator <<(std::ostream &os, Scope const &scope);
