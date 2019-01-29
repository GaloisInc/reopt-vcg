
#include <cstdio> // printf etc.
#include <cstdint> // types
#include <string> // std::strtoul 
#include <iostream>

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

bool
getInstruction(vadd::instruction_t &Instr, uint64_t &Size, llvm::ArrayRef<uint8_t> Bytes, uint64_t Address,
               llvm::X86Disassembler::DisassemblerMode fMode, llvm::raw_ostream &VStream, llvm::raw_ostream &CStream);

/*
// Global state for use in byteReader
struct reader_state {
    uint8_t *buffer;
    size_t buflen;
    uint64_t base_address;

    reader_state(uint8_t *bytes, size_t len, uint64_t addr)
        : buffer(bytes), buflen(len), base_address(addr) {}
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
*/


// int
// byteReader(const void *arg, uint8_t *byte, uint64_t address)
// {
//     const struct reader_state *st = (const struct reader_state *) arg;
//     size_t offset = address - st->base_address;
//     if (offset >= st->buflen) {
//         std::cerr << "byteReader: Attempt to read past end of buffer at " << std::hex << address;
//         return -1;
//     }

//     *byte = st->buffer[offset];
//     return 0;
// }

// void
// dlog(void *arg, const char *log)
// {
//     std::cerr << log << std::endl;
// }

/*
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

    return 0;
}
*/
    
void
print_instruction(uint64_t offset, uint64_t size
                  , const vadd::instruction_t& x, std::ostream &out
                  , const llvm::MCRegisterInfo *reginfo
                  , llvm::MCInstrInfo *mii /* Just to print opcode name */)
{
    out << "(" << offset << " " << size << " ";
    out << "(instruction " << mii->getName(x.instructionID).data();

    for(const auto &op : x.operands) {
        out << " ";
        print_sexp(op, out, reginfo);
    }
    out << "))" << std::endl;
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
    std::string Error;
    
    auto target = llvm::TargetRegistry::lookupTarget(triple_name, Error);
    if (!target) {
        std::cerr << "lookupTarget: " << Error << std::endl;
        llvm::TargetRegistry::printRegisteredTargetsForVersion(llvm::errs());
        return 1;
    }

    auto reginfo = target->createMCRegInfo(triple_name);
    if (! reginfo) {
        std::cerr << "Couldn't create reginfo" << std::endl;
        return 1;
    }

    auto mii = target->createMCInstrInfo();
    if (! mii) {
        std::cerr << "Couldn't create mii" << std::endl;
        return 1;
    }

    if (argc < 2) {
        std::cerr << "Usage: " << argv[0] << " nbytes" << std::endl;
        return 1;
    }

    size_t nbytes = std::strtoull(argv[1], NULL, 0);
    uint8_t *raw_bytes = new uint8_t[nbytes];
    std::cin.read((char *)(raw_bytes), nbytes);
    
    if (!std::cin) {
        std::cerr << "error: only " << std::cin.gcount() << " bytes could be read,  expected " << nbytes << std::endl;
        return 1;
    }

    llvm::ArrayRef<uint8_t> bytes_array(raw_bytes, nbytes);
    uint64_t offset = 0;

    std::cout << "(";
    while(offset < nbytes) {
        vadd::instruction_t inst;
        uint64_t size;
        
        bool ret = getInstruction(inst, size, bytes_array, offset
                                  , llvm::X86Disassembler::MODE_64BIT
                                  , llvm::nulls(), llvm::nulls() );
        
        if (ret) {
            std::cout << "(unknown-byte " << bytes_array[0] << " " << size << ")" << std::endl;
            size = 1; // trim off just 1 byte
        } else {
            print_instruction(offset, size, inst, std::cout, reginfo, mii);
        }
        
        offset += size;
        bytes_array = bytes_array.slice(size);
    }
    std::cout << ")" << std::endl;
    
    return 0;
}

