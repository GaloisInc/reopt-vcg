
#include "InstructionsImports.lean.inc"

namespace x86
namespace k_x86_semantics

open gen

def dummyInstruction := instruction.mk "DUMMY" []

def all_instructions := [ dummyInstruction
#include "InstructionsList.lean.inc"
                       ]
    
end k_x86_semantics
end x86
