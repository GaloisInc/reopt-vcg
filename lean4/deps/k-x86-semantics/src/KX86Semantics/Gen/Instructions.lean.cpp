
#include "InstructionsImports.lean.inc"

namespace x86
namespace k-x86-semantics

def all_instructions := [
#include "InstructionsList.lean.inc"
                       ]
    
end k-x86-semantics
end x86
