// -*- c++ -*-

#include <cstdint>
#include <vector>
#include <string>
#include <iostream>

// LLVM stuff

// #include "X86RegisterInfo.h"
#include "X86MCTargetDesc.h"
#include "llvm/MC/MCRegisterInfo.h"

#include "object.h" // to get lean::object

namespace vadd {
using operand_t = lean::object *;
using reg_t     = llvm::MCPhysReg; // object *;

// inductive operand_value
//   | register : register -> operand_value
//   | segment  : Option register -> register -> operand_value
//   | immediate : ℕ -> ℕ -> operand_value
//   | rel_immediate : ℕ -> ℕ -> ℕ -> operand_value
//   | memloc : Option register -> Option register -> ℕ -> Option register -> ℕ -> operand_value

operand_t mk_operand_register(const std::string &type, reg_t r);
operand_t mk_operand_segment(const std::string &type, reg_t m_s, reg_t r);
operand_t mk_operand_immediate(const std::string &type, uint64_t n, uint64_t v);
operand_t mk_operand_rel_immediate(const std::string &type, uint64_t off, uint64_t n, uint64_t v);
operand_t mk_operand_memloc(const std::string &type, reg_t seg, reg_t b, uint64_t s, reg_t i, uint64_t d);

#define MAX_N_OPERANDS 5 // FIXME: maybe only 3?

class instruction_t {
 public:
    uint16_t instructionID; // as from InternalInstruction
    unsigned Flags;
    uint64_t noperands = 0;
    operand_t operands[MAX_N_OPERANDS];

    void setOpcode(uint16_t i) { instructionID = i; }
    uint16_t getOpcode(void) { return instructionID; }
    
    void addOperand(operand_t op) { assert(noperands < MAX_N_OPERANDS); operands[noperands++] = op; }
    void setFlags(unsigned f) { Flags = f; }
};
   
} // namespace vadd
