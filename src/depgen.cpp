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
  auto root = decl_cast<TranslationUnitDecl>(ast->root);
  auto modules = std::vector<ModuleDecl*>();

  for (auto &decl : root->decls)
  {
    if (decl->kind() == Decl::Module)
    {
      modules.push_back(decl_cast<ModuleDecl>(decl));
    }
  }

  auto fout = std::ofstream(target);

  if (!fout)
  {
    cerr << "unable to create depfile '" << target << "'\n";

    return;
  }

  fout << outfile << ":";

  for (auto &module : modules)
  {
    fout << " " << module->file();

    if (&module != &modules.back())
      fout << " \\";

    fout << '\n';
  }

  fout.close();
}
