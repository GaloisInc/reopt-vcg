#include <cctype>
#include <algorithm>

#include "X86DisassemblerDecoder.h"
#include "X86MCTargetDesc.h"

#include "llvm-c/Target.h"

#include "llvm/Support/raw_os_ostream.h"
#include "llvm/MC/MCDisassembler/MCDisassembler.h"
#include "llvm/MC/MCInst.h"
#include "llvm/MC/MCInstrInfo.h"
#include "llvm/MC/MCInstrDesc.h"
#include "llvm/MC/MCInstPrinter.h"
#include "llvm/MC/MCContext.h"
#include "llvm/Support/TargetRegistry.h"

#include "Instruction.h"

#pragma clang diagnostic push // clang complains about variadic macros
#pragma clang diagnostic ignored "-Wvariadic-macros"
#pragma clang diagnostic ignored "-Wgnu-zero-variadic-macro-arguments"
#include "object.h"
#pragma clang diagnostic pop

using namespace lean;

bool
getInstruction(vadd::instruction_t &Instr, uint64_t &Size, llvm::ArrayRef<uint8_t> Bytes, uint64_t Address,
               llvm::X86Disassembler::DisassemblerMode fMode, llvm::raw_ostream &VStream, llvm::raw_ostream &CStream);

// -----------------------------------------------------------------------------
// Imported (from instruction.lean)

namespace decodex86 {
namespace exported {

extern object* mk_reg(object* x_0, object* x_1, object* x_2, object* x_3);
extern object* mk_some_reg(object* x_0);
extern object* mk_none_reg;

extern object* mk_operand_register(object* x_0, object* x_1);
extern object* mk_operand_segment(object* x_0, object* x_1, object* x_2);
extern object* mk_operand_immediate(object* x_0, object* x_1, object* x_2);
extern object* mk_operand_rel_immediate(object* x_0, object* x_1, object* x_2, object* x_3);
extern object* mk_operand_memloc(object* x_0, object* x_1, object* x_2, object* x_3, object* x_4, object* x_5);

extern object* mk_instruction_0(object *nbytes, object *m);
extern object* mk_instruction_1(object *nbytes, object *m, object *o1);
extern object* mk_instruction_2(object *nbytes, object *m, object *o1, object *o2);
extern object* mk_instruction_3(object *nbytes, object *m, object *o1, object *o2, object *o3);

extern object* mk_decode_success(object *i);
extern object* mk_decode_failure(object *n);

}
}

namespace vadd {

// -----------------------------------------------------------------------------
// LLVM Support
    
// Basically a singleton class which holds regs to the various LLVM
// datastructures
class LLVMMeta {
public:
    llvm::MCInstrInfo *mii;
    
    LLVMMeta() {
        /* Lots of boilerplate to create the disassembler */
        llvm::Triple triple(llvm::Twine(llvm::Triple::normalize("x86_64-generic-linux-elf")));
        const std::string triple_name = triple.getTriple();

        LLVMInitializeX86TargetInfo();
        LLVMInitializeX86Target();
        LLVMInitializeX86TargetMC();
        std::string Error;
    
        auto target = llvm::TargetRegistry::lookupTarget(triple_name, Error);
        assert(target);
        // if (!target) {
        //     std::cerr << "lookupTarget: " << Error << std::endl;
        //     llvm::TargetRegistry::printRegisteredTargetsForVersion(llvm::errs());
        //     return 1;
        // }

        auto reginfo = target->createMCRegInfo(triple_name);
        assert(reginfo);
        // if (! reginfo) {
        //     std::cerr << "Couldn't create reginfo" << std::endl;
        //     return 1;
        // }
        
        mii = target->createMCInstrInfo();
        assert(mii);
        // if (! mii) {
        //     std::cerr << "Couldn't create mii" << std::endl;
        //     return 1;
        // }

        // Initialise all the register names, starting from 1 (0 is NoRegister)
        for(unsigned int i = 1; i < llvm::X86::NUM_TARGET_REGS; i++)
            init_regname(reginfo, i);
        
        for(unsigned int i = 1; i < llvm::X86::NUM_TARGET_REGS; i++)
            init_reg(reginfo, i);
    }

    // returns NULL if r == llvm::NoRegister
    object *get_reg(llvm::MCPhysReg r) {
        object *ret = reg_cache[r];
        if (ret) inc(ret);
        return ret;
    }
    
    object *get_option_reg(llvm::MCPhysReg r) {
        object *reg = reg_cache[r];
        if (reg) {
            inc(reg);
            return decodex86::exported::mk_some_reg(reg);
        } else {
            inc(decodex86::exported::mk_none_reg);
            return decodex86::exported::mk_none_reg;
        }
    }

    // FIXME: maybe have a table for these as well?  There are about
    // 16k mnemnonics though ...
    object *get_mnemonic(uint16_t instID) {
        return mk_string(mii->getName(instID).data());
    }
    
private:
    object *reg_name_cache[llvm::X86::NUM_TARGET_REGS]; // NULL for the NoRegister
    object *reg_cache[llvm::X86::NUM_TARGET_REGS]; // NULL for the NoRegister

    void init_regname(llvm::MCRegisterInfo *reginfo, llvm::MCPhysReg r) {
        // from http://www.cplusplus.com/reference/locale/tolower/
        std::locale loc;
        const char *regname = reginfo->getName(r);
        std::string lc_regname(regname);

        std::transform(lc_regname.begin(), lc_regname.end(), lc_regname.begin(),
                       [](unsigned char c){ return std::tolower(c); });
        reg_name_cache[r] = mk_string(lc_regname);
    }
                         
    // Make a decodex86 register 
    void init_reg(llvm::MCRegisterInfo *reginfo, llvm::MCPhysReg reg) {
        unsigned top = reg;
    
        for (llvm::MCSuperRegIterator I(reg, reginfo); I.isValid(); ++I)
            if (reginfo->isSuperRegister(top, *I))
                top = *I;

        unsigned subidx = reginfo->getSubRegIndex(top, reg);
        object *topN        = reg_name_cache[top];
        inc(topN);
        
        object *regN        = reg_name_cache[reg];
        inc(regN);
        
        object *reg_idx_sz  = box(0);
        object *reg_idx_off = box(0);
        if (subidx) {
            reg_idx_sz = mk_nat_obj(reginfo->getSubRegIdxSize(subidx));
            reg_idx_off = mk_nat_obj(reginfo->getSubRegIdxOffset(subidx));
        }
        
        reg_cache[reg] = decodex86::exported::mk_reg(topN, regN, reg_idx_sz, reg_idx_off);
    }
};

// We want to delay initializing the object until after lean has
// started (not sure what leans initialisation looks like)
static LLVMMeta &
llvmMeta() {
    static LLVMMeta theLLVMMeta;
    return theLLVMMeta;
}

// -----------------------------------------------------------------------------
// Calling into lean-generated functionx

operand_t
mk_operand_register(const std::string &type, reg_t r) {
    object *type_obj = mk_string(type);
    object *reg_obj  = llvmMeta().get_reg(r);
    assert(reg_obj);

    return decodex86::exported::mk_operand_register(type_obj, reg_obj);
}
    
operand_t
mk_operand_segment(const std::string &type, reg_t m_s, reg_t r) {
    object *type_obj = mk_string(type);
    object *seg_obj  = llvmMeta().get_option_reg(m_s);
    object *reg_obj  = llvmMeta().get_reg(r);
    assert(reg_obj);

    return decodex86::exported::mk_operand_segment(type_obj, seg_obj, reg_obj);
}

operand_t
mk_operand_immediate(const std::string &type, uint64_t n, uint64_t v) {
    object *type_obj = mk_string(type);
    object *n_obj  = mk_nat_obj(n);
    object *v_obj  = mk_nat_obj(v);

    return decodex86::exported::mk_operand_immediate(type_obj, n_obj, v_obj);
}

operand_t
mk_operand_rel_immediate(const std::string &type, uint64_t off, uint64_t n, uint64_t v) {
    object *type_obj = mk_string(type);
    object *off_obj = mk_nat_obj(off);
    object *n_obj  = mk_nat_obj(n);
    object *v_obj  = mk_nat_obj(v);

    return decodex86::exported::mk_operand_rel_immediate(type_obj, off_obj, n_obj, v_obj);
}

operand_t
mk_operand_memloc(const std::string &type, reg_t seg, reg_t b, uint64_t s, reg_t i, uint64_t d)  {
    object *type_obj = mk_string(type);
    object *seg_obj  = llvmMeta().get_option_reg(seg);
    object *b_obj    = llvmMeta().get_option_reg(b);
    object *s_obj    = mk_nat_obj(s);
    object *i_obj    = llvmMeta().get_option_reg(i);
    object *d_obj    = mk_nat_obj(d);
    return decodex86::exported::mk_operand_memloc(type_obj, seg_obj, b_obj, s_obj, i_obj, d_obj);
}

// -----------------------------------------------------------------------------
// Exported (to lean)

// byte_array -> N -> Option instruction
obj_res
decode(b_obj_arg buffer_o, b_obj_arg offset_o)
{
    size_t nbytes      = sarray_size(buffer_o);
    uint8_t *raw_bytes = sarray_cptr<uint8_t>(buffer_o);
    uint64_t offset    = nat2uint64(offset_o);
    
    llvm::ArrayRef<uint8_t> bytes_array(raw_bytes, nbytes);
    vadd::instruction_t inst;
    uint64_t size;

    bool ret = getInstruction(inst, size, bytes_array.slice(offset), 0
                              , llvm::X86Disassembler::MODE_64BIT
                              , llvm::nulls(), llvm::nulls() );

    object *nbytes_o = mk_nat_obj(size);
    if (ret) {
        // Failed to decode.
        return decodex86::exported::mk_decode_failure(nbytes_o);
    } else {
        object *mnemonic_o = llvmMeta().get_mnemonic(inst.instructionID);
        object *inst_o = NULL;
        
        switch (inst.noperands) {
        case 0: inst_o = decodex86::exported::mk_instruction_0(nbytes_o, mnemonic_o); break;
        case 1:
            inst_o = decodex86::exported::mk_instruction_1(nbytes_o, mnemonic_o
                                                           , inst.operands[0]);
            break;
        case 2:
            inst_o = decodex86::exported::mk_instruction_2(nbytes_o, mnemonic_o
                                                           , inst.operands[0], inst.operands[1]);
            break;
        case 3:
            inst_o = decodex86::exported::mk_instruction_3(nbytes_o, mnemonic_o
                                                           , inst.operands[0]
                                                           , inst.operands[1]
                                                           , inst.operands[2]);
            break;
        default: lean_unreachable();
        }
        return decodex86::exported::mk_decode_success(inst_o);
    }
}

} // namespace vadd
