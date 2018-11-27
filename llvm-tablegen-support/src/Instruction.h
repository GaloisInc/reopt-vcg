// -*- c++ -*-

#include <cstdint>
#include <vector>
#include <string>
#include <iostream>

// #include "X86RegisterInfo.h"
#include "X86MCTargetDesc.h"
#include "llvm/MC/MCRegisterInfo.h"

namespace vadd {

// c.f. https://github.com/sean-parent/sean-parent.github.io/blob/master/papers-and-presentations.md (Runtime Polymorphism)

    
// c.f. X86::reg from llvm/MC/MCRegisterInfo.h

// Unifies a bunch of different addressing modes etc., basic idea is

// baseseg:basereg + scale * indexreg + displacement

// Basic idea here is to have this class handle all mem handling etc.
class operand_t {
public:
    template <typename T>
    operand_t(T x) : self_(std::make_shared<model<T>>(std::move(x))) {}

    friend void print_sexp(const operand_t& x, std::ostream &out, const llvm::MCRegisterInfo *reginfo)
    { x.self_->print_sexp_(out, reginfo); }
private:
    struct concept_t {
        virtual ~concept_t() = default;
        virtual void print_sexp_(std::ostream& out, const llvm::MCRegisterInfo *reginfo) const = 0;
    };
    template <typename T>
    struct model final : concept_t {
        model(T x) : data_(std::move(x)) {}
        void print_sexp_(std::ostream& out, const llvm::MCRegisterInfo *reginfo) const override
        { print_sexp(data_, out, reginfo); }

        T data_;
    };

    std::shared_ptr<const concept_t> self_;
};

class instruction_t {
 public:
    uint16_t instructionID; // as from InternalInstruction
    unsigned Flags;
    std::vector<operand_t> operands;

    void setOpcode(uint16_t i) { instructionID = i; }
    uint16_t getOpcode(void) { return instructionID; }
    
    void addOperand(operand_t op) { operands.push_back(op); }
    void setFlags(unsigned f) { Flags = f; }
};
   
} // namespace vadd
