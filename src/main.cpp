//
// zacc
//
// Copyright (C) 2020 Peter Niekamp. All rights reserved.
//
// This file is part of zaalang, which is BSD-2-Clause licensed.
// See http://opensource.org/licenses/BSD-2-Clause
//

#include "sema.h"
#include "diag.h"
#include "lexer.h"
#include "parser.h"
#include "typer.h"
#include "lower.h"
#include "codegen.h"
#include "toolchain.h"
#include <iostream>
#include <string>
#include <cstring>
#include <algorithm>

using namespace std;

//|//////////////////// main ////////////////////////////////////////////////
int main(int argc, char *argv[])
{
  string file = "";

  for(int i = 0, j = 0; i < argc; ++i)
  {    
    if (argv[i][0] == '-')
    {
      if ((argv[i][1] == 'I' || argv[i][1] == 'L' || argv[i][1] == 'l') && argv[i][2] == 0)
        ++i;

      continue;
    }

    if (j == 1)
      file = argv[i];

    ++j;
  }

  Diag diag("zacc");

  if (file == "")
  {
    cerr << "no input files" << endl;
    exit(1);
  }

  try
  {
    Sema sema;

    for(int i = 0; i < argc; ++i)
    {
      if (strncmp(argv[i], "-I", 2) == 0)
        sema.add_include_path(argv[i][2] != 0 ? argv[i] + 2 : argv[++i]);
    }

    parse(file, sema, diag);

#if 0
    dump_ast(sema.ast);
    cout << "--" << endl;
#endif

    if (diag.has_errored())
    {
      cerr << diag << endl;

      exit(1);
    }

    typer(sema.ast, sema, diag);

#if 0
    dump_ast(sema.ast);
    cout << "--" << endl;
#endif

    GenOpts opts;
    opts.modulename = file;

    for(int i = 0; i < argc; ++i)
    {
      if (strcmp(argv[i], "-emit-asm") == 0)
        opts.outputtype = GenOpts::OutputType::EmitAsm;

      if (strcmp(argv[i], "-emit-ll") == 0)
        opts.outputtype = GenOpts::OutputType::EmitLL;

      if (strcmp(argv[i], "-g") == 0)
        opts.debuginfo = GenOpts::DebugInfo::Yes;

      if (strcmp(argv[i], "-O1") == 0)
        opts.optlevel = GenOpts::OptLevel::Less;

      if (strcmp(argv[i], "-O2") == 0)
        opts.optlevel = GenOpts::OptLevel::Default;

      if (strcmp(argv[i], "-O3") == 0)
        opts.optlevel = GenOpts::OptLevel::Aggressive;

      if (strcmp(argv[i], "-c") == 0)
        opts.linker = false;

      if (strcmp(argv[i], "-dump-mir") == 0)
        opts.dump_mir = true;
    }

    if (opts.outputtype != GenOpts::OutputType::EmitObj)
      opts.linker = false;

    ToolChain toolchain(opts.triple);

    if (!toolchain)
    {
      cerr << "unable to initialise toolchain" << endl;
      exit(1);
    }

    string intfile = filename(toolchain, file, opts.outputtype);

    codegen(sema.ast, intfile, opts, diag);

    cerr << diag << endl;

    if (diag.has_errored())
      exit(1);

    if (opts.linker)
    {
      string outfile = filename(toolchain, file, ToolChain::Executable);

      vector<string> libraries;

      for(int i = 0; i < argc; ++i)
      {
        if (strncmp(argv[i], "-L", 2) == 0)
          toolchain.add_library_path(argv[i][2] != 0 ? argv[i] + 2 : argv[++i]);

        if (strncmp(argv[i], "-l", 2) == 0)
          libraries.push_back(argv[i][2] != 0 ? argv[i] + 2 : argv[++i]);
      }

      toolchain.ld(intfile, outfile, libraries);
    }
  }
  catch(exception &e)
  {
    cerr << diag << endl;

    cerr << "Internal Compiler Error: " << e.what() << endl;
  }
}
