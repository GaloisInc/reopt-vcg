#include <cctype>
#include <algorithm>

#include "llvm-c/Target.h"

#include "llvm/Support/raw_os_ostream.h"
#include "llvm/MC/MCDisassembler/MCDisassembler.h"
#include "llvm/MC/MCInst.h"
#include "llvm/MC/MCInstrInfo.h"
#include "llvm/MC/MCInstrDesc.h"
#include "llvm/MC/MCInstPrinter.h"
#include "llvm/MC/MCContext.h"
#include "llvm/Support/TargetRegistry.h"

#pragma clang diagnostic push // clang complains about variadic macros
#pragma clang diagnostic ignored "-Wvariadic-macros"
#pragma clang diagnostic ignored "-Wgnu-zero-variadic-macro-arguments"
#include "lean/object.h"
#pragma clang diagnostic pop

using namespace lean;

extern "C" {
    
extern object* mcinst_exported_mk_decode_success(object *i, object *n);
extern object* mcinst_exported_mk_decode_failure(object *n);

}

namespace vadd {

// -----------------------------------------------------------------------------
// LLVM Support
    
// Basically a singleton class which holds regs to the various LLVM
// datastructures
class LLVMMCInstMeta {
public:
    llvm::MCInstrInfo *mii;
    llvm::MCDisassembler *mcdis;
    llvm::MCInstPrinter *mcp;

    LLVMMCInstMeta() {
        /* Lots of boilerplate to create the disassembler */
        llvm::Triple triple(llvm::Twine(llvm::Triple::normalize("x86_64-generic-linux-elf")));
        const std::string triple_name = triple.getTriple();

        LLVMInitializeX86TargetInfo();
        LLVMInitializeX86Target();
        LLVMInitializeX86TargetMC();
        LLVMInitializeX86Disassembler();
        std::string Error;

        auto target = llvm::TargetRegistry::lookupTarget(triple_name, Error);
        assert(target);

        mii = target->createMCInstrInfo();
        assert(mii);

        auto reginfo = target->createMCRegInfo(triple_name);
        assert(reginfo);

        const llvm::MCTargetOptions mcOptions;
        auto asminfo = target->createMCAsmInfo(*reginfo, triple_name, mcOptions);
        assert(asminfo);

        mcp = target->createMCInstPrinter(triple, 0, *asminfo, *mii, *reginfo);
        assert(mcp);

        auto sti = target->createMCSubtargetInfo(triple_name, "", "");
        assert(sti);
        auto ctxt = new llvm::MCContext(asminfo, reginfo, /* MOFI, obj file info */ NULL);
        assert(ctxt);
        mcdis = target->createMCDisassembler(*sti, *ctxt);
        assert(mcdis);
    }

    int decode(std::string &out,
               uint64_t &nbytes,
               llvm::ArrayRef<uint8_t> buffer,
               uint64_t base_address) {
        llvm::MCInst insn;

        if (mcdis->getInstruction(insn, nbytes, buffer, base_address, llvm::nulls())
            == llvm::MCDisassembler::Fail) {
            // std::cerr << "Could not decode" << std::endl;
            return 1;
        }

        llvm::raw_string_ostream out_stream(out);
        mcp->printInst(&insn, base_address, "", mcdis->getSubtargetInfo(), out_stream);
        out_stream.flush();
        return 0;
    }
};

// We want to delay initializing the object until after lean has
// started (not sure what leans initialisation looks like)
static LLVMMCInstMeta &
llvmMeta() {
    static LLVMMCInstMeta theLLVMMCInstMeta;
    return theLLVMMCInstMeta;
}

// -----------------------------------------------------------------------------
// Exported (to lean)

// byte_array -> N -> N -> Option instruction
extern "C" obj_res
vadd_mcinst_decode(b_obj_arg buffer_o, b_obj_arg offset_o, b_obj_arg base_address_o)
{
    size_t nbytes      = sarray_size(buffer_o);
    uint8_t *raw_bytes = sarray_cptr(buffer_o);
    uint64_t offset    = unbox(offset_o);
    uint64_t base_address = unbox(base_address_o);
    
    llvm::ArrayRef<uint8_t> bytes_array(raw_bytes, nbytes);
    std::string res;
    uint64_t size;

    bool ret = llvmMeta().decode(res, size, bytes_array.slice(offset), base_address);
    
    object *nbytes_o = mk_nat_obj(size);
    if (ret) {
        // Failed to decode.
        return mcinst_exported_mk_decode_failure(nbytes_o);
    } else {
        object *inst_o = mk_string(res);     
        return mcinst_exported_mk_decode_success(inst_o, nbytes_o);
    }
}

} // namespace vadd
