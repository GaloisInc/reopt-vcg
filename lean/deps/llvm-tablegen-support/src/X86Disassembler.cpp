// -*- c-basic-offset: 2 -*-
//===-- X86Disassembler.cpp - Disassembler for x86 and x86_64 -------------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//

//
// This file was modified from the LLVM distribution to give more
// useful output.  In particular, memory addresses are explicitly
// grouped, rather than just appending the corresponding opcodes.
// See Instruction.h to see what the print_sexp is used for.

//
// This file is part of the X86 Disassembler.
// It contains code to translate the data produced by the decoder into
//  MCInsts.
//
//
// The X86 disassembler is a table-driven disassembler for the 16-, 32-, and
// 64-bit X86 instruction sets.  The main decode sequence for an assembly
// instruction in this disassembler is:
//
// 1. Read the prefix bytes and determine the attributes of the instruction.
//    These attributes, recorded in enum attributeBits
//    (X86DisassemblerDecoderCommon.h), form a bitmask.  The table CONTEXTS_SYM
//    provides a mapping from bitmasks to contexts, which are represented by
//    enum InstructionContext (ibid.).
//
// 2. Read the opcode, and determine what kind of opcode it is.  The
//    disassembler distinguishes four kinds of opcodes, which are enumerated in
//    OpcodeType (X86DisassemblerDecoderCommon.h): one-byte (0xnn), two-byte
//    (0x0f 0xnn), three-byte-38 (0x0f 0x38 0xnn), or three-byte-3a
//    (0x0f 0x3a 0xnn).  Mandatory prefixes are treated as part of the context.
//
// 3. Depending on the opcode type, look in one of four ClassDecision structures
//    (X86DisassemblerDecoderCommon.h).  Use the opcode class to determine which
//    OpcodeDecision (ibid.) to look the opcode in.  Look up the opcode, to get
//    a ModRMDecision (ibid.).
//
// 4. Some instructions, such as escape opcodes or extended opcodes, or even
//    instructions that have ModRM*Reg / ModRM*Mem forms in LLVM, need the
//    ModR/M byte to complete decode.  The ModRMDecision's type is an entry from
//    ModRMDecisionType (X86DisassemblerDecoderCommon.h) that indicates if the
//    ModR/M byte is required and how to interpret it.
//
// 5. After resolving the ModRMDecision, the disassembler has a unique ID
//    of type InstrUID (X86DisassemblerDecoderCommon.h).  Looking this ID up in
//    INSTRUCTIONS_SYM yields the name of the instruction and the encodings and
//    meanings of its operands.
//
// 6. For each operand, its encoding is an entry from OperandEncoding
//    (X86DisassemblerDecoderCommon.h) and its type is an entry from
//    OperandType (ibid.).  The encoding indicates how to read it from the
//    instruction; the type indicates how to interpret the value once it has
//    been read.  For example, a register operand could be stored in the R/M
//    field of the ModR/M byte, the REG field of the ModR/M byte, or added to
//    the main opcode.  This is orthogonal from its meaning (an GPR or an XMM
//    register, for instance).  Given this information, the operands can be
//    extracted and interpreted.
//
// 7. As the last step, the disassembler translates the instruction information
//    and operands into a format understandable by the client - in this case, an
//    MCInst for use by the MC infrastructure.
//
// The disassembler is broken broadly into two parts: the table emitter that
// emits the instruction decode tables discussed above during compilation, and
// the disassembler itself.  The table emitter is documented in more detail in
// utils/TableGen/X86DisassemblerEmitter.h.
//
// X86Disassembler.cpp contains the code responsible for step 7, and for
//   invoking the decoder to execute steps 1-6.
// X86DisassemblerDecoderCommon.h contains the definitions needed by both the
//   table emitter and the disassembler.
// X86DisassemblerDecoder.h contains the public interface of the decoder,
//   factored out into C for possible use by other projects.
// X86DisassemblerDecoder.c contains the source code of the decoder, which is
//   responsible for steps 1-6.
//
//===----------------------------------------------------------------------===//

#include <locale> // tolower
#include "X86BaseInfo.h"
#include "X86DisassemblerDecoder.h"
#include "llvm/Support/TargetRegistry.h"
#include "llvm/Support/raw_ostream.h"

#include "Instruction.h"

using namespace llvm;
using namespace llvm::X86Disassembler;

// c.f. Metadata.cpp
const char *
operandType(uint16_t instrID, unsigned int operand);

#define DEBUG_TYPE "x86-disassembler"

// StringRef llvm::X86Disassembler::GetInstrName(unsigned Opcode,
//                                                 const void *mii) {
//   const MCInstrInfo *MII = static_cast<const MCInstrInfo *>(mii);
//   return MII->getName(Opcode);
// }

#define debug(s) LLVM_DEBUG(Debug(__FILE__, __LINE__, s));

namespace llvm {

// Fill-ins to make the compiler happy.  These constants are never actually
//   assigned; they are just filler to make an automatically-generated switch
//   statement work.
namespace X86 {
  enum {
    BX_SI = 500,
    BX_DI = 501,
    BP_SI = 502,
    BP_DI = 503,
    sib   = 504,
    sib64 = 505
  };
}

}

static void
print_register_lowercase(unsigned reg, std::ostream &out, const llvm::MCRegisterInfo *reginfo)
{
  // from http://www.cplusplus.com/reference/locale/tolower/
  std::locale loc;
  for(const char *regname = reginfo->getName(reg);
      *regname;
      regname++) {
    out << std::tolower(*regname,loc);  
  }
}

static void
print_sexp_for_register(unsigned reg, std::ostream &out, const llvm::MCRegisterInfo *reginfo)
{
  if (reg == X86::NoRegister)
    out << "no-register";
  else {
    // This assumes we have a top register.
    unsigned top = reg;
    
    for (llvm::MCSuperRegIterator I(reg, reginfo); I.isValid(); ++I)
        if (reginfo->isSuperRegister(top, *I))
            top = *I;

    unsigned subidx = reginfo->getSubRegIndex(top, reg);
    out << "(register ";
    print_register_lowercase(top, out, reginfo);
    out << " ";
    print_register_lowercase(reg, out, reginfo);
    out << " ";
    
    if (subidx) 
        out << reginfo->getSubRegIdxSize(subidx) << " " << reginfo->getSubRegIdxOffset(subidx);
    else
        out << "0 0";

    out << ")";
  }
}


// fwd decl.
static bool translateInstruction(vadd::instruction_t &target,
                                 InternalInstruction &source);

namespace {
struct Region {
  ArrayRef<uint8_t> Bytes;
  uint64_t Base;
  Region(ArrayRef<uint8_t> Bytes, uint64_t Base) : Bytes(Bytes), Base(Base) {}
};
} // end anonymous namespace

/// A callback function that wraps the readByte method from Region.
///
/// @param Arg      - The generic callback parameter.  In this case, this should
///                   be a pointer to a Region.
/// @param Byte     - A pointer to the byte to be read.
/// @param Address  - The address to be read.
static int regionReader(const void *Arg, uint8_t *Byte, uint64_t Address) {
  auto *R = static_cast<const Region *>(Arg);
  ArrayRef<uint8_t> Bytes = R->Bytes;
  unsigned Index = Address - R->Base;
  if (Bytes.size() <= Index)
    return -1;
  *Byte = Bytes[Index];
  return 0;
}

/// logger - a callback function that wraps the operator<< method from
///   raw_ostream.
///
/// @param arg      - The generic callback parameter.  This should be a pointe
///                   to a raw_ostream.
/// @param log      - A string to be logged.  logger() adds a newline.
static void logger(void* arg, const char* log) {
  if (!arg)
    return;

  raw_ostream &vStream = *(static_cast<raw_ostream*>(arg));
  vStream << log << "\n";
}

//
// Public interface for the disassembler
//

bool
getInstruction(vadd::instruction_t &Instr, uint64_t &Size, ArrayRef<uint8_t> Bytes, uint64_t Address,
               DisassemblerMode fMode, raw_ostream &VStream, raw_ostream &CStream) {
  InternalInstruction InternalInstr;

  dlog_t LoggerFn = logger;
  if (&VStream == &nulls())
    LoggerFn = nullptr; // Disable logging completely if it's going to nulls().

  Region R(Bytes, Address);

  int Ret = decodeInstruction(&InternalInstr, regionReader, (const void *)&R,
                              LoggerFn, (void *)&VStream,
                              NULL, Address, fMode);

  if (Ret) {
    Size = InternalInstr.readerCursor - Address;
    return true;
  } else {
    Size = InternalInstr.length;
    bool Ret = translateInstruction(Instr, InternalInstr);
    if (!Ret) {
      unsigned Flags = X86::IP_NO_PREFIX;
      if (InternalInstr.hasAdSize)
        Flags |= X86::IP_HAS_AD_SIZE;
      if (!InternalInstr.mandatoryPrefix) {
        if (InternalInstr.hasOpSize)
          Flags |= X86::IP_HAS_OP_SIZE;
        if (InternalInstr.repeatPrefix == 0xf2)
          Flags |= X86::IP_HAS_REPEAT_NE;
        else if (InternalInstr.repeatPrefix == 0xf3 &&
                 // It should not be 'pause' f3 90
                 InternalInstr.opcode != 0x90)
          Flags |= X86::IP_HAS_REPEAT;
        if (InternalInstr.hasLockPrefix)
          Flags |= X86::IP_HAS_LOCK;
      }
      Instr.setFlags(Flags);
    }
    return Ret;
  }
}
        
struct reg_t {
    llvm::MCPhysReg r;
    reg_t(llvm::MCPhysReg r) : r(r) {}
};

void
print_sexp(const reg_t& x, std::ostream& out, const llvm::MCRegisterInfo *reginfo)
{
    print_sexp_for_register(x.r, out, reginfo);
}

//
// Private code that translates from struct InternalInstructions to MCInsts.
//

/// translateRegister - Translates an internal register to the appropriate LLVM
///   register, and appends it as an operand to an MCInst.
///
/// @param mcInst     - The MCInst to append to.
/// @param reg        - The Reg to append.
static void translateRegister(vadd::instruction_t &Inst, Reg reg, const char *optype) {
#define ENTRY(x) X86::x,
  static constexpr MCPhysReg llvmRegnums[] = {ALL_REGS};
#undef ENTRY

  MCPhysReg llvmRegnum = llvmRegnums[reg];
  Inst.addOperand(optype, reg_t(llvmRegnum));
}

/// tryAddingSymbolicOperand - trys to add a symbolic operand in place of the
/// immediate Value in the MCInst.
///
/// @param Value      - The immediate Value, has had any PC adjustment made by
///                     the caller.
/// @param isBranch   - If the instruction is a branch instruction
/// @param Address    - The starting address of the instruction
/// @param Offset     - The byte offset to this immediate in the instruction
/// @param Width      - The byte width of this immediate in the instruction
///
/// If the getOpInfo() function was set when setupForSymbolicDisassembly() was
/// called then that function is called to get any symbolic information for the
/// immediate in the instruction using the Address, Offset and Width.  If that
/// returns non-zero then the symbolic information it returns is used to create
/// an MCExpr and that is added as an operand to the MCInst.  If getOpInfo()
/// returns zero and isBranch is true then a symbol look up for immediate Value
/// is done and if a symbol is found an MCExpr is created with that, else
/// an MCExpr with the immediate Value is created.  This function returns true
/// if it adds an operand to the MCInst and false otherwise.
/*
static bool tryAddingSymbolicOperand(int64_t Value, bool isBranch,
                                     uint64_t Address, uint64_t Offset,
                                     uint64_t Width, MCInst &MI,
                                     const MCDisassembler *Dis) {
  return Dis->tryAddingSymbolicOperand(MI, Value, Address, isBranch,
                                       Offset, Width);
}
*/

/// tryAddingPcLoadReferenceComment - trys to add a comment as to what is being
/// referenced by a load instruction with the base register that is the rip.
/// These can often be addresses in a literal pool.  The Address of the
/// instruction and its immediate Value are used to determine the address
/// being referenced in the literal pool entry.  The SymbolLookUp call back will
/// return a pointer to a literal 'C' string if the referenced address is an
/// address into a section with 'C' string literals.
/*
static void tryAddingPcLoadReferenceComment(uint64_t Address, uint64_t Value,
                                            const void *Decoder) {
  const MCDisassembler *Dis = static_cast<const MCDisassembler*>(Decoder);
  Dis->tryAddingPcLoadReferenceComment(Value, Address);
}
*/

static const uint8_t segmentRegnums[SEG_OVERRIDE_max] = {
  X86::NoRegister,        // SEG_OVERRIDE_NONE
  X86::CS,
  X86::SS,
  X86::DS,
  X86::ES,
  X86::FS,
  X86::GS
};

struct segment_index_op_t {
  llvm::MCPhysReg segmentreg;// = llvm::X86::NoRegister;
  llvm::MCPhysReg basereg;// = llvm::X86::NoRegister;
  segment_index_op_t(llvm::MCPhysReg segmentreg, llvm::MCPhysReg basereg)
    : segmentreg(segmentreg), basereg(basereg) {}
};

void
print_sexp(const segment_index_op_t& x, std::ostream& out, const llvm::MCRegisterInfo *reginfo)
{
    out << "(segment-index ";
    print_sexp_for_register(x.segmentreg, out, reginfo);
    out << " ";
    print_sexp_for_register(x.basereg, out, reginfo);
    out << ")";
}

/// translateSrcIndex   - Appends a source index operand to an MCInst.
///
/// @param mcInst       - The MCInst to append to.
/// @param insn         - The internal instruction.
static bool translateSrcIndex(vadd::instruction_t &Inst, InternalInstruction &insn, const char *optype) {
  unsigned baseRegNo;

  if (insn.mode == MODE_64BIT)
    baseRegNo = insn.hasAdSize ? X86::ESI : X86::RSI;
  else if (insn.mode == MODE_32BIT)
    baseRegNo = insn.hasAdSize ? X86::SI : X86::ESI;
  else {
    assert(insn.mode == MODE_16BIT);
    baseRegNo = insn.hasAdSize ? X86::ESI : X86::SI;
  }

  Inst.addOperand(optype, segment_index_op_t(segmentRegnums[insn.segmentOverride], baseRegNo));
  
  return false;
}

/// translateDstIndex   - Appends a destination index operand to an MCInst.
///
/// @param mcInst       - The MCInst to append to.
/// @param insn         - The internal instruction.

static bool translateDstIndex(vadd::instruction_t &Inst, InternalInstruction &insn, const char *optype) {
  unsigned baseRegNo;

  if (insn.mode == MODE_64BIT)
    baseRegNo = insn.hasAdSize ? X86::EDI : X86::RDI;
  else if (insn.mode == MODE_32BIT)
    baseRegNo = insn.hasAdSize ? X86::DI : X86::EDI;
  else {
    assert(insn.mode == MODE_16BIT);
    baseRegNo = insn.hasAdSize ? X86::EDI : X86::DI;
  }
  Inst.addOperand(optype, reg_t(baseRegNo));
  return false;
}

// struct dup_t {
//   unsigned int which;
//   dup_t(unsigned int which) : which (which) {}
// };

// void
// print_sexp(const dup_t& x, std::ostream& out, const llvm::MCRegisterInfo *reginfo)
// {
//     out << "(dup " << x.which << ")";
// }

uint64_t
sign_extend(uint64_t val, int nbytes)
{
    int shift_bits = 64 - nbytes * 8;
    return (((int64_t) (val << shift_bits)) >> shift_bits);
}

// May be sign extended, dep. on value.
struct immediate_t {
  uint64_t nbytes;
  uint64_t value;
  immediate_t(uint64_t nbytes, uint64_t value)
    : nbytes(nbytes), value(value) {}    
};

void
print_sexp(const immediate_t& x, std::ostream& out, const llvm::MCRegisterInfo *reginfo)
{
    out << "(immediate " << x.nbytes << " " << x.value << ")";
}

struct rel_immediate_t {
  uint64_t pc_off;
  uint64_t nbytes;
  uint64_t value;
  rel_immediate_t(uint64_t pc_off, uint64_t nbytes, uint64_t value)
    : pc_off(pc_off), nbytes(nbytes), value(value) {}
};
    
void
print_sexp(const rel_immediate_t& x, std::ostream& out, const llvm::MCRegisterInfo *reginfo)
{
    out << "(rel-immediate " << x.pc_off << " " << x.nbytes << " " << x.value << ")";
}

class memloc_op_t {
 public:
    llvm::MCPhysReg segmentreg = llvm::X86::NoRegister;
    llvm::MCPhysReg basereg = llvm::X86::NoRegister;
    uint64_t scale = 1;
    llvm::MCPhysReg indexreg = llvm::X86::NoRegister;
    uint64_t displacement;

    memloc_op_t() {}
    
    memloc_op_t(llvm::MCPhysReg segmentreg, 
                 llvm::MCPhysReg basereg, 
                 uint64_t scale, 
                 llvm::MCPhysReg indexreg,
                 uint64_t displacement)
        : segmentreg(segmentreg), basereg(basereg), scale(scale)
        , indexreg(indexreg), displacement(displacement)
    {}
};

void
print_sexp(const memloc_op_t& x, std::ostream& out, const llvm::MCRegisterInfo *reginfo)
{
    out << "(memloc ";
    print_sexp_for_register(x.segmentreg, out, reginfo);
    out << " ";
    print_sexp_for_register(x.basereg, out, reginfo);
    out << " " << x.scale << " ";
    print_sexp_for_register(x.indexreg, out, reginfo);
    out << " " << x.displacement << ")";
}

/// translateImmediate  - Appends an immediate operand to an MCInst.
///
/// @param mcInst       - The Inst to append to.
/// @param immediate    - The immediate value to append.
/// @param operand      - The operand, as stored in the descriptor table.
/// @param insn         - The internal instruction.
static void translateImmediate(vadd::instruction_t &Inst, uint64_t immediate,
                               const OperandSpecifier &operand,
                               InternalInstruction &insn, const char *optype) {
  // Sign-extend the immediate if necessary.    
  OperandType type = (OperandType)operand.type;
  /* Possible encodings
    { ENCODING_IB, TYPE_AVX512ICC },
    { ENCODING_IB, TYPE_IMM },
    { ENCODING_IB, TYPE_IMM3 },
    { ENCODING_IB, TYPE_IMM5 },
    { ENCODING_IB, TYPE_REL },
    { ENCODING_IB, TYPE_UIMM8 },
    { ENCODING_IB, TYPE_XMM },
    { ENCODING_IB, TYPE_YMM },
    { ENCODING_ID, TYPE_IMM },
    { ENCODING_ID, TYPE_REL },
    { ENCODING_IO, TYPE_IMM },
    { ENCODING_IRC, TYPE_IMM },
    { ENCODING_IW, TYPE_IMM },
    { ENCODING_IW, TYPE_REL },
    { ENCODING_Ia, TYPE_MOFFS },
    { ENCODING_Iv, TYPE_IMM },
    
    XMM, YNN are used to get a register using bits 7-4.
    REL is signed PC relative (relative to next insn)
    IMM can be sign extended (actual use dep. on instruction?)
    UIMM8 is an unsigned 8 bit value.
    IMM3 and IMM5 seem to be for 8bit CCs
    MOFFS is an unsigned absolute address, along with a segment register.

    We need to sign-extend for REL and IMM only
  */
  switch (type) {
  default:
    llvm_unreachable("unknown type");
    return;
    
  case TYPE_XMM:
    Inst.addOperand(optype, reg_t(X86::XMM0 + (immediate >> 4)));
    return;
  case TYPE_YMM:
    Inst.addOperand(optype, reg_t(X86::YMM0 + (immediate >> 4)));
    return;

  case TYPE_MOFFS: {
    MCPhysReg seg = segmentRegnums[insn.segmentOverride];
    Inst.addOperand(optype, memloc_op_t(seg, llvm::X86::NoRegister, 1, llvm::X86::NoRegister, immediate));
    return;
  }
    
  case TYPE_REL: /* fallthru */
  case TYPE_IMM: {
    uint64_t nbytes = 0;
    /* sign extend */
    switch (operand.encoding) {
    default:
      break;
    case ENCODING_Iv:
      nbytes = insn.displacementSize;
      break;
    case ENCODING_IB:
      nbytes = 1;
      break;
    case ENCODING_IW:
      nbytes = 2;
      break;
    case ENCODING_ID:
      nbytes = 4;
      break;
    case ENCODING_IO:
      nbytes = 8;
      break;
    }

    immediate = sign_extend(immediate, nbytes);
  /*  if(!tryAddingSymbolicOperand(immediate + pcrel, isBranch, insn.startLocation,
                               insn.immediateOffset, insn.immediateSize,
                               mcInst, Dis))
  */
    if (type == TYPE_REL)
      Inst.addOperand(optype, rel_immediate_t(insn.startLocation + insn.length, nbytes, immediate)); // FIXME: 1 here?
    else
      Inst.addOperand(optype, immediate_t(nbytes, immediate)); // FIXME: 1 here?
    return;;
  }
    
  case TYPE_UIMM8: /* fallthru */
  case TYPE_IMM3:  /* fallthru */
  case TYPE_IMM5:
    Inst.addOperand(optype, immediate_t(1, immediate)); // FIXME: 1 here?
    return;
  }
}
 

/// translateRMRegister - Translates a register stored in the R/M field of the
///   ModR/M byte to its LLVM equivalent and appends it to an MCInst.
/// @param mcInst       - The MCInst to append to.
/// @param insn         - The internal instruction to extract the R/M field
///                       from.
/// @return             - 0 on success; -1 otherwise
static bool translateRMRegister(vadd::instruction_t &Inst,
                                InternalInstruction &insn,
                                const char *optype) {
  if (insn.eaBase == EA_BASE_sib || insn.eaBase == EA_BASE_sib64) {
    debug("A R/M register operand may not have a SIB byte");
    return true;
  }

  switch (insn.eaBase) {
  default:
    debug("Unexpected EA base register");
    return true;
  case EA_BASE_NONE:
    debug("EA_BASE_NONE for ModR/M base");
    return true;
#define ENTRY(x) case EA_BASE_##x:
  ALL_EA_BASES
#undef ENTRY
    debug("A R/M register operand may not have a base; "
          "the operand must be a register.");
    return true;
#define ENTRY(x)                                                      \
  case EA_REG_##x:                                                    \
    Inst.addOperand(optype, reg_t(X86::x)); break;
  ALL_REGS
#undef ENTRY
  }

  return false;
}


/// translateRMMemory - Translates a memory operand stored in the Mod and R/M
///   fields of an internal instruction (and possibly its SIB byte) to a memory
///   operand in LLVM's format, and appends it to an MCInst.
///
/// @param mcInst       - The MCInst to append to.
/// @param insn         - The instruction to extract Mod, R/M, and SIB fields
///                       from.
/// @return             - 0 on success; nonzero otherwise
static bool translateRMMemory(vadd::instruction_t &Inst, InternalInstruction &insn, const char *optype) {
  // Addresses in an MCInst are represented as five operands:
  //   1. basereg       (register)  The R/M base, or (if there is a SIB) the
  //                                SIB base
  //   2. scaleamount   (immediate) 1, or (if there is a SIB) the specified
  //                                scale amount
  //   3. indexreg      (register)  x86_registerNONE, or (if there is a SIB)
  //                                the index (which is multiplied by the
  //                                scale amount)
  //   4. displacement  (immediate) 0, or the displacement if there is one
  //   5. segmentreg    (register)  x86_registerNONE for now, but could be set
  //                                if we have segment overrides
  memloc_op_t mloc;

  if (insn.eaBase == EA_BASE_sib || insn.eaBase == EA_BASE_sib64) {
    if (insn.sibBase != SIB_BASE_NONE) {
      switch (insn.sibBase) {
      default:
        debug("Unexpected sibBase");
        return true;
#define ENTRY(x)                                          \
      case SIB_BASE_##x:                                  \
        mloc.basereg = X86::x; break;
      ALL_SIB_BASES
#undef ENTRY
      }
    }
    
    if (insn.sibIndex != SIB_INDEX_NONE) {
      switch (insn.sibIndex) {
      default:
        debug("Unexpected sibIndex");
        return true;
#define ENTRY(x)                                          \
      case SIB_INDEX_##x:                                 \
        mloc.indexreg = X86::x; break;
      EA_BASES_32BIT
      EA_BASES_64BIT
      REGS_XMM
      REGS_YMM
      REGS_ZMM
#undef ENTRY
      }
    } else {
      // Use EIZ/RIZ for a few ambiguous cases where the SIB byte is present,
      // but no index is used and modrm alone should have been enough.
      // -No base register in 32-bit mode. In 64-bit mode this is used to
      //  avoid rip-relative addressing.
      // -Any base register used other than ESP/RSP/R12D/R12. Using these as a
      //  base always requires a SIB byte.
      // -A scale other than 1 is used.
      if (insn.sibScale != 1 ||
          (insn.sibBase == SIB_BASE_NONE && insn.mode != MODE_64BIT) ||
          (insn.sibBase != SIB_BASE_NONE &&
           insn.sibBase != SIB_BASE_ESP && insn.sibBase != SIB_BASE_RSP &&
           insn.sibBase != SIB_BASE_R12D && insn.sibBase != SIB_BASE_R12))
        mloc.indexreg = insn.addressSize == 4 ? X86::EIZ : X86::RIZ;
      
    }

    mloc.scale = insn.sibScale;
  } else {
    switch (insn.eaBase) {
    case EA_BASE_NONE:
      if (insn.eaDisplacement == EA_DISP_NONE) {
        debug("EA_BASE_NONE and EA_DISP_NONE for ModR/M base");
        return true;
      }
      if (insn.mode == MODE_64BIT) {
        // Section 2.2.1.6
        mloc.basereg = insn.addressSize == 4 ? X86::EIP : X86::RIP;
      }
      break;
    case EA_BASE_BX_SI:
      mloc.basereg = X86::BX;
      mloc.indexreg = X86::SI;
      break;
    case EA_BASE_BX_DI:
      mloc.basereg = X86::BX;
      mloc.indexreg = X86::DI;
      break;
    case EA_BASE_BP_SI:
      mloc.basereg = X86::BP;
      mloc.indexreg = X86::SI;
      break;
    case EA_BASE_BP_DI:
      mloc.basereg = X86::BP;
      mloc.indexreg = X86::DI;
      break;
    default:
      switch (insn.eaBase) {
      default:
        debug("Unexpected eaBase");
        return true;
        // Here, we will use the fill-ins defined above.  However,
        //   BX_SI, BX_DI, BP_SI, and BP_DI are all handled above and
        //   sib and sib64 were handled in the top-level if, so they're only
        //   placeholders to keep the compiler happy.
#define ENTRY(x)                                        \
      case EA_BASE_##x:                                 \
        mloc.basereg = X86::x; break;
      ALL_EA_BASES
#undef ENTRY
#define ENTRY(x) case EA_REG_##x:
      ALL_REGS
#undef ENTRY
        debug("A R/M memory operand may not be a register; "
              "the base field must be a base.");
        return true;
      }
    }
  }

  mloc.displacement = insn.displacement;
  mloc.segmentreg = segmentRegnums[insn.segmentOverride];
 
  Inst.addOperand(optype, mloc);
  return false;
}

/// translateRM - Translates an operand stored in the R/M (and possibly SIB)
///   byte of an instruction to LLVM form, and appends it to an MCInst.
///
/// @param mcInst       - The MCInst to append to.
/// @param operand      - The operand, as stored in the descriptor table.
/// @param insn         - The instruction to extract Mod, R/M, and SIB fields
///                       from.
/// @return             - 0 on success; nonzero otherwise
static bool translateRM(vadd::instruction_t &Inst, const OperandSpecifier &operand,
                        InternalInstruction &insn, const char *optype) {
  switch (operand.type) {
  default:
    debug("Unexpected type for a R/M operand");
    return true;
  case TYPE_R8:
  case TYPE_R16:
  case TYPE_R32:
  case TYPE_R64:
  case TYPE_Rv:
  case TYPE_MM64:
  case TYPE_XMM:
  case TYPE_YMM:
  case TYPE_ZMM:
  case TYPE_VK:
  case TYPE_DEBUGREG:
  case TYPE_CONTROLREG:
  case TYPE_BNDR:
    return translateRMRegister(Inst, insn, optype);
  case TYPE_M:
  case TYPE_MVSIBX:
  case TYPE_MVSIBY:
  case TYPE_MVSIBZ:
    return translateRMMemory(Inst, insn, optype);
  }
}

/// translateFPRegister - Translates a stack position on the FPU stack to its
///   LLVM form, and appends it to an MCInst.
///
/// @param mcInst       - The MCInst to append to.
/// @param stackPos     - The stack position to translate.
static void translateFPRegister(vadd::instruction_t &Inst,
                                uint8_t stackPos,
                                const char *optype) {
  Inst.addOperand(optype, reg_t(X86::ST0 + stackPos));
}

/// translateMaskRegister - Translates a 3-bit mask register number to
///   LLVM form, and appends it to an MCInst.
///
/// @param mcInst       - The MCInst to append to.
/// @param maskRegNum   - Number of mask register from 0 to 7.
/// @return             - false on success; true otherwise.
static bool translateMaskRegister(vadd::instruction_t &Inst,
                                  uint8_t maskRegNum,
                                  const char *optype) {
  if (maskRegNum >= 8) {
    debug("Invalid mask register number");
    return true;
  }

  Inst.addOperand(optype, reg_t(X86::K0 + maskRegNum));
  return false;
}

/// translateOperand - Translates an operand stored in an internal instruction
///   to LLVM's format and appends it to an MCInst.
///
/// @param mcInst       - The MCInst to append to.
/// @param operand      - The operand, as stored in the descriptor table.
/// @param insn         - The internal instruction.
/// @return             - false on success; true otherwise.
static bool translateOperand(vadd::instruction_t &Inst, const OperandSpecifier &operand,
                             InternalInstruction &insn, const char* optype) {
  switch (operand.encoding) {
  default:
    debug("Unhandled operand encoding during translation");
    return true;
  case ENCODING_REG:
    translateRegister(Inst, insn.reg, optype);
    return false;
  case ENCODING_WRITEMASK:
    return translateMaskRegister(Inst, insn.writemask, optype);
  CASE_ENCODING_RM:
  CASE_ENCODING_VSIB:
    return translateRM(Inst, operand, insn, optype);
  case ENCODING_IB:
  case ENCODING_IW:
  case ENCODING_ID:
  case ENCODING_IO:
  case ENCODING_Iv:
  case ENCODING_Ia:
    translateImmediate(Inst,
                       insn.immediates[insn.numImmediatesTranslated++],
                       operand,
                       insn, optype);
    return false;
  case ENCODING_IRC:
    Inst.addOperand(optype, immediate_t(1, insn.RC));
    return false;
  case ENCODING_SI:
    return translateSrcIndex(Inst, insn, optype);
  case ENCODING_DI:
    return translateDstIndex(Inst, insn, optype);
  case ENCODING_RB:
  case ENCODING_RW:
  case ENCODING_RD:
  case ENCODING_RO:
  case ENCODING_Rv:
    translateRegister(Inst, insn.opcodeRegister, optype);
    return false;
  case ENCODING_FP:
    translateFPRegister(Inst, insn.modRM & 7, optype);
    return false;
  case ENCODING_VVVV:
    translateRegister(Inst, insn.vvvv, optype);
    return false;
  case ENCODING_DUP:
    // We ignore duplicate operands.
    // FIXME: is this OK?
    return false; // translateOperand(Inst, insn.operands[operand.type - TYPE_DUP0], insn, optype);
  }
}

/// translateInstruction - Translates an internal instruction and all its
///   operands to an MCInst.
///
/// @param mcInst       - The MCInst to populate with the instruction's data.
/// @param insn         - The internal instruction.
/// @return             - false on success; true otherwise.
bool
translateInstruction(vadd::instruction_t &Inst, InternalInstruction &insn) {
  if (!insn.spec) {
    debug("Instruction has no specification");
    return true;
  }

  Inst.setOpcode(insn.instructionID);
  // If when reading the prefix bytes we determined the overlapping 0xf2 or 0xf3
  // prefix bytes should be disassembled as xrelease and xacquire then set the
  // opcode to those instead of the rep and repne opcodes.
  if (insn.xAcquireRelease) {
    if(Inst.getOpcode() == X86::REP_PREFIX)
      Inst.setOpcode(X86::XRELEASE_PREFIX);
    else if(Inst.getOpcode() == X86::REPNE_PREFIX)
      Inst.setOpcode(X86::XACQUIRE_PREFIX);
  }

  insn.numImmediatesTranslated = 0;

  unsigned int opno = 0;
  for (const auto &Op : insn.operands) {
    if (Op.encoding != ENCODING_NONE) {
      const char *optype = operandType(insn.instructionID, opno++);
      if (translateOperand(Inst, Op, insn, optype)) {
        return true;
      }
    }
  }

  return false;
}
