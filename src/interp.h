//
// interp.h
//
// Copyright (C) 2020 Peter Niekamp. All rights reserved.
//
// This file is part of zaalang, which is BSD-2-Clause licensed.
// See http://opensource.org/licenses/BSD-2-Clause
//

#pragma once

#include "query.h"
#include "lower.h"

//-------------------------- EvalResult -------------------------------------
//---------------------------------------------------------------------------

struct EvalResult
{
  Type *type;
  Expr *value;

  explicit operator bool() const { return value; }
};

//-------------------------- Evaluate ---------------------------------------
//---------------------------------------------------------------------------

EvalResult evaluate(Scope const &scope, MIR const &mir, TypeTable &typetable, class Diag &diag, SourceLocation loc);
EvalResult evaluate(Scope const &scope, FnSig const &callee, std::vector<EvalResult> const &parms, TypeTable &typetable, class Diag &diag, SourceLocation loc);
EvalResult evaluate(Scope const &scope, Expr *expr, std::unordered_map<Decl*, MIR::Fragment> const &symbols, TypeTable &typetable, class Diag &diag, SourceLocation loc);
