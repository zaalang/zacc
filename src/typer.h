//
// typer.h
//
// Copyright (c) 2020-2023 Peter Niekamp. All rights reserved.
//
// This file is part of zaalang, which is BSD-2-Clause licensed.
// See http://opensource.org/licenses/BSD-2-Clause
//

#pragma once

#include "ast.h"

//-------------------------- Typer ------------------------------------------
//---------------------------------------------------------------------------

void typer(AST *ast, class Sema &sema, class Diag &diag);
