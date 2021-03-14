//
// lifetime.h
//
// Copyright (C) 2021 Peter Niekamp. All rights reserved.
//
// This file is part of zaalang, which is BSD-2-Clause licensed.
// See http://opensource.org/licenses/BSD-2-Clause
//

#pragma once

#include "mir.h"

//-------------------------- Lifetime ---------------------------------------
//---------------------------------------------------------------------------

void lifetime(MIR const &mir, class TypeTable &typetable, class Diag &diag);
