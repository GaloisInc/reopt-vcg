-- -*- lean4-mode -*-

#define XSTR(x) #x
#define STR(x) XSTR(x)

import KX86Semantics.Compat

namespace x86
namespace k_x86_semantics
namespace gen

open mc_semantics
open mc_semantics.type
open reg
open semantics

#include STR(INSTRUCTION.lean)

end gen
end k_x86_semantics
end x86
