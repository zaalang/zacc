//
// semantic.h
//
// Copyright (C) 2020 Peter Niekamp. All rights reserved.
//
// This file is part of zaalang, which is BSD-2-Clause licensed.
// See http://opensource.org/licenses/BSD-2-Clause
//

#pragma once

#include "ast.h"
#include "query.h"

//-------------------------- semantic ---------------------------------------
//---------------------------------------------------------------------------

void semantic(ModuleDecl *module, class Sema &sema, class Diag &diag);
void semantic(Scope const &scope, Decl *decl, class Sema &sema, class Diag &diag);
