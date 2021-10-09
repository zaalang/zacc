//
// mangle.h
//
// Copyright (C) 2020 Peter Niekamp. All rights reserved.
//
// This file is part of zaalang, which is BSD-2-Clause licensed.
// See http://opensource.org/licenses/BSD-2-Clause
//

#pragma once

#include <string>
#include <string_view>
#include <variant>

class Decl;
class Stmt;
class FunctionDecl;

//-------------------------- Mangle -----------------------------------------
//---------------------------------------------------------------------------

std::string get_mangled_name(FunctionDecl const *fn);
std::string get_mangled_name(FunctionDecl const *fn, std::string_view name);

std::string mangle_scope(std::variant<Decl*, Stmt*> const &scope);

