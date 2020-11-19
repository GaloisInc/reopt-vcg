/* Extra metadata from the JSON */
#include <stdio.h>
#include <stdint.h>
#include <cassert>

#define GET_INSTRINFO_ENUM
#include "../llvm-files/X86GenInstrInfo.inc"

struct operand_desc {
    unsigned int noperands;
    unsigned int operand_idx;
};


// least-ugly option, basically
# pragma clang diagnostic push 
# pragma clang diagnostic ignored "-Wc99-extensions" 

#include "operand_table.inc"

# pragma clang diagnostic pop 


const char *
operandType(uint16_t instrID, unsigned int operand)
{
    assert(instrID < llvm::X86::INSTRUCTION_LIST_END);
    // assert(operand < iArr[instrID].noperands);
    if (operand >= iArr[instrID].noperands) {
        fprintf(stderr, "Error, operand idx %d out of bounds for %d\n", operand, instrID);
        assert(0);
    }
    unsigned int idx = iArr[instrID].operand_idx + operand;
    llvm::X86::DAGOperands::DAGOperandType typ = oArr[idx];
    return oNArr[typ];
}
    

