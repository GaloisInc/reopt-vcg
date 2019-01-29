
#include <cstdio> // printf etc.
#include <cstdint> // types
#include <string> // std::strtoul 
#include <iostream>

 #include <X86DisassemblerDecoder.h>
#include <llvm-c/Target.h>

#include "llvm/Support/raw_os_ostream.h"
#include "llvm/MC/MCDisassembler/MCDisassembler.h"
#include "llvm/MC/MCInst.h"
#include "llvm/MC/MCInstrInfo.h"
#include "llvm/MC/MCInstrDesc.h"
#include "llvm/MC/MCInstPrinter.h"
#include "llvm/MC/MCContext.h"
#include "llvm/Support/TargetRegistry.h"


// Global state for use in byteReader
struct reader_state {
    llvm::ArrayRef<uint8_t> buffer;
    uint64_t base_address;

    reader_state(uint8_t *bytes, size_t len, uint64_t addr)
        : buffer(bytes, len), base_address(addr) {}
};


// x86 instructions are at most 16 bytes.
struct reader_state *
initState(int argc, char **argv)
{
    if (argc < 2) {
        std::cerr << "Usage: " << argv[0] << " address b1 b2 b3 ..." << std::endl;
        exit(1);
    }

    uint64_t base_address = std::strtoull(argv[1], NULL, 16);
    size_t buflen = argc - 2;
    uint8_t *buf = (uint8_t *) calloc(buflen, 1);
    
    for (unsigned int i = 0; i < buflen; i++)
        buf[i] = std::strtoull(argv[i + 2], NULL, 16);

    return new reader_state(buf, buflen, base_address);
}
/*
int
byteReader(const void *arg, uint8_t *byte, uint64_t address)
{
    const struct reader_state *st = (const struct reader_state *) arg;
    size_t offset = address - st->base_address;
    if (offset >= st->buflen) {
        std::cerr << "byteReader: Attempt to read past end of buffer at " << std::hex << address;
        return -1;
    }

    *byte = st->buffer[offset];
    return 0;
}
*/  

void
dlog(void *arg, const char *log)
{
    std::cerr << log << std::endl;
}

/* Protocol: line oriented, first line is

   read ->
   address nbytes binary_data...\n

   write <- (nothing)

  following lines are 

  read -> 
  0xaddress (<= 18 bytes)\n
  write <-
  sexp \n

*/

int go(struct reader_state *st, llvm::MCInstrInfo *mii, llvm::MCDisassembler *mcdis, llvm::MCInstPrinter *mcp)
{

    llvm::MCInst insn;
    uint64_t nbytes; 
        
    if (mcdis->getInstruction(insn, nbytes, st->buffer, st->base_address, llvm::errs(), llvm::errs()) == llvm::MCDisassembler::Fail) {
        std::cerr << "Could not decode" << std::endl;
        return 1;
    } 

    std::cerr << "Got an instruction length " << nbytes << " bytes." << std::endl;
    insn.dump_pretty(llvm::errs()); llvm::errs() << "\n";
    mcp->printInst(&insn, llvm::errs(), "", mcdis->getSubtargetInfo());
    llvm::errs() << "\n";
   
    auto desc = mii->get(insn.getOpcode());
    for (auto oi : desc.operands()) {
        llvm::errs() << "oi: '" << (int) oi.OperandType << "'\n";
    }

    llvm::errs() << mcp->getOpcodeName(insn.getOpcode()) << "\n";
    llvm::errs() << "size: " << insn.size() << "\n";
    for (auto op : insn) {
        if (op.isReg()) {
            mcp->printRegName(llvm::errs(), op.getReg());
            llvm::errs() << "\n";
        } else
            llvm::errs() << "<other>\n";
    }


    

    
    /*
    while(true) {
        char buf[19];
        char *str_end = NULL;
        
        std::cin.getline(buf, sizeof(buf));
        uint64_t startLoc = std::strtoull(buf, &str_end, 16);

        llvm::MCInst insn;
        uint64_t nbytes; 
        
        if (mcdis->getInstruction(insn, nbytes, st->buffer, startLoc, llvm::errs(), llvm::errs()) == llvm::MCDisassembler::Fail) {
            std::cerr << "Could not decode" << std::endl;
            return 1;
        } 

        std::cerr << "Got an instruction length " << nbytes << " bytes." << std::endl;
        insn.dump_pretty(llvm::errs());
    }
    */
    return 0;
}


// c.f. tools/llvm-cfi-verify/lib/FileAnalysis.cpp
int main(int argc, char **argv)
{
    /* Lots of boilerplate to create the disassembler */
    llvm::Triple triple(llvm::Twine(llvm::Triple::normalize("x86_64-generic-linux-elf")));
    const std::string triple_name = triple.getTriple();
    
    LLVMInitializeX86TargetInfo();
    LLVMInitializeX86Target();
    LLVMInitializeX86TargetMC();
    LLVMInitializeX86Disassembler();
    std::string Error;
    
    //const llvm::Target *target = llvm::TargetRegistry::lookupTarget("X86", Error);
    auto target = llvm::TargetRegistry::lookupTarget(triple_name, Error);
    if (!target) {
        std::cerr << "lookupTarget: " << Error << std::endl;
        llvm::TargetRegistry::printRegisteredTargetsForVersion(llvm::errs());
        return 1;
    }
    // std::cerr << "Got target for " << triple.str() << " " << target->getName() << std::endl;

    auto reginfo = target->createMCRegInfo(triple_name);
    if (! reginfo) {
        std::cerr << "Couldn't create reginfo" << std::endl;
        return 1;
    }

    auto asminfo = target->createMCAsmInfo(*reginfo, triple_name);
    if (! asminfo) {
        std::cerr << "Couldn't create reginfo" << std::endl;
        return 1;
    }
    
    auto sti = target->createMCSubtargetInfo(triple_name, "", "");    
    if (! sti) {
        std::cerr << "Couldn't create subtarget" << std::endl;
        return 1;
    }

    auto mii = target->createMCInstrInfo();
    if (! mii) {
        std::cerr << "Couldn't create mii" << std::endl;
        return 1;
    }

    auto ctxt = new llvm::MCContext(asminfo, reginfo, /* MOFI, obj file info */ NULL); 
    if (! ctxt) {
        std::cerr << "Couldn't create context" << std::endl;
        return 1;
    }

    auto mcp = target->createMCInstPrinter(triple, 0, *asminfo, *mii, *reginfo);
    if (! mcp) {
        std::cerr << "Couldn't create inst printer" << std::endl;
        return 1;
    }
    
    auto mcdis = target->createMCDisassembler(*sti, *ctxt);
    if (! mcdis) {
        std::cerr << "Couldn't create mcdis" << std::endl;
        return 1;
    }
    
    struct reader_state *st = initState(argc, argv);
    if (! st) {
        std::cerr << "Could not initState" << std::endl;
        return 1;
    }

    go(st, mii, mcdis, mcp);
    
        /*

    while(true) {
        char buf[19];
        char *str_end = NULL;
        struct llvm::X86Disassembler::InternalInstruction insn;
        
        std::cin.getline(buf, sizeof(buf));
        std::cerr << "Read a line" << std::endl;
        
        uint64_t startLoc = std::strtoull(buf, &str_end, 16);

        if (llvm::X86Disassembler::decodeInstruction(&insn, byteReader, (void *) st,
                                                       dlog, NULL, NULL, startLoc,
                                                       llvm::X86Disassembler::MODE_64BIT)) {
            std::cerr << "Could not decode" << std::endl;
            return 1;
        } 

        std::cerr << "Got an instruction, " << insn.length << " bytes." << std::endl;
        } */
    return 0;
}

