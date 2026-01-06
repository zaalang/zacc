//
// ast.cpp
//
// Copyright (c) 2020-2026 Peter Niekamp. All rights reserved.
//
// This file is part of zaalang, which is BSD-2-Clause licensed.
// See http://opensource.org/licenses/BSD-2-Clause
//

#include "ast.h"
#include <iostream>

using namespace std;

//|--------------------- AST ------------------------------------------------
//|--------------------------------------------------------------------------

//|///////////////////// AST::Constructor ///////////////////////////////////
AST::AST(Decl *root)
  : root(root)
{
}

//|///////////////////// AST::dump //////////////////////////////////////////
void AST::dump() const
{
  root->dump(0);
}

//|///////////////////// dump_ast ///////////////////////////////////////////
void dump_ast(AST const *ast)
{
  if (ast)
    ast->dump();
}
