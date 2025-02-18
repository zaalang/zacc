//
// depgen.h
//
// Copyright (c) 2025-2025 Peter Niekamp. All rights reserved.
//
// This file is part of zaalang, which is BSD-2-Clause licensed.
// See http://opensource.org/licenses/BSD-2-Clause
//

#pragma once

#include "ast.h"

//-------------------------- DepGen -----------------------------------------
//---------------------------------------------------------------------------

void depgen(AST *ast, std::string const &outfile, std::string const &target);
