//
// copier.h
//
// Copyright (c) 2021-2023 Peter Niekamp. All rights reserved.
//
// This file is part of zaalang, which is BSD-2-Clause licensed.
// See http://opensource.org/licenses/BSD-2-Clause
//

#pragma once

#include "ast.h"

//-------------------------- Copier -----------------------------------------
//---------------------------------------------------------------------------

Decl *copier(Decl *root, std::vector<Expr*> const &substitutions, class Diag &diag);
