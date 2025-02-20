//
// depgen.cpp
//
// Copyright (c) 2020-2024 Peter Niekamp. All rights reserved.
//
// This file is part of zaalang, which is BSD-2-Clause licensed.
// See http://opensource.org/licenses/BSD-2-Clause
//

#include "depgen.h"
#include <iostream>
#include <fstream>

using namespace std;

//|--------------------- DepGen ---------------------------------------------
//|--------------------------------------------------------------------------

//|///////////////////// depgen /////////////////////////////////////////////
void depgen(AST *ast, string const &outfile, string const &target)
{
  auto fout = std::ofstream(target);

  if (!fout)
  {
    cerr << "unable to create depfile '" << target << "'\n";

    return;
  }

  fout << outfile << ": \\\n";

  for (auto &decl : decl_cast<TranslationUnitDecl>(ast->root)->decls)
  {
    if (decl->kind() == Decl::Module)
    {
      fout << " " << decl_cast<ModuleDecl>(decl)->file() << " \\\n";
    }
  }

  fout << '\n';

  fout.close();
}
