//
// parser.h
//
// Copyright (C) 2020-2022 Peter Niekamp. All rights reserved.
//
// This file is part of zaalang, which is BSD-2-Clause licensed.
// See http://opensource.org/licenses/BSD-2-Clause
//

#pragma once

#include "ast.h"
#include <string>

//-------------------------- Parser -----------------------------------------
//---------------------------------------------------------------------------

bool load(ModuleDecl *module, class Sema &sema, class Diag &diag);
bool parse(std::string const &path, class Sema &sema, class Diag &diag);
