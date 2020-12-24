
import KX86Semantics.Compat

namespace x86
namespace k_x86_semantics

-- FIXME: maybe import over copying?
open mc_semantics
open mc_semantics.type
open mc_semantics.float_class
open reg
open semantics

-- local
infix:20 " ≠ " => neq

infix:20 " .= " => set

def nat_to_bv {w:Nat} (n:Nat) : expression (bv w) := prim.bv_nat w n

------------------------------------------------------------------------
-- syscall definition

def syscall : instruction :=
  definst "syscall" $ mk_pattern (record_event event.syscall)

------------------------------------------------------------------------
-- leave definition
-- High Level Procedure Exit

def leaveq : instruction :=
 definst "leaveq" $ do
   instr_pat $
    let action : semantics Unit := do
     rsp .= rbp;
     let v ← eval (expression.read (bv 64) rsp);
     rsp .= coe rsp + nat_to_bv 8;
     rbp .= v
    action

------------------------------------------------------------------------
-- push definition
-- Push Word => doubleword or Quadword Onto the Stack
 
def pushq : instruction :=
 definst "pushq" $ do
   instr_pat $ fun (value: expression (bv 64)) =>
    let action : semantics Unit := do
     rsp .= coe rsp - nat_to_bv 8;
     lhs.write_addr rsp _ .= value
    action
 
def pushw : instruction :=
 definst "pushw" $ do
   instr_pat $ fun (value: expression (bv 32)) =>
    let action : semantics Unit := do
     rsp .= coe rsp - nat_to_bv 4;
     lhs.write_addr rsp _ .= value
    action

------------------------------------------------------------------------
-- pop definition

-- Pop a Value from the Stack
def popq : instruction :=
 definst "popq" $ do
   instr_pat $ fun (dest: lhs (bv 64)) =>
    let action : semantics Unit := do
     let v ← eval (expression.read (bv 64) rsp);
     rsp  .= coe rsp + nat_to_bv 8;
     dest .= v
    action

def popw : instruction :=
 definst "popw" $ do
   instr_pat $ fun (dest: lhs (bv 32)) => 
    let action : semantics Unit := do
     let v ← eval (expression.read (bv 32) rsp);
     rsp  .= coe rsp + nat_to_bv 4;
     dest .= v
    action
   

------------------------------------------------------------------------
-- call definition
-- Call Procedure

def callq : instruction :=
 definst "callq" $ do
   instr_pat $ fun (off : imm int) =>
    let action : semantics Unit := do
     let off_bv <- eval (handleImmediateWithSignExtend off 32 64);
     let v      <- eval expression.get_rip;
     record_event (event.call (add v off_bv))
    action
   ;
   -- indirect via mem or reg
   instr_pat $ fun (v : expression (bv 64)) =>
     record_event (event.call v)
   

------------------------------------------------------------------------
-- jmp definition
-- Jump
def jmpq : instruction :=
 definst "jmpq" $ do
   instr_pat $ fun (off : imm int) =>
    let action : semantics Unit := do
     let off_bv <- eval (handleImmediateWithSignExtend off 32 64);
     let v      <- eval expression.get_rip;
     record_event (event.jmp (add v off_bv))
    action
   ;
   instr_pat $ fun (v : expression (bv 64)) =>
     record_event (event.jmp v)
   

------------------------------------------------------------------------
-- Condition codes
--
-- Conditional codes for instructions, some of these have multiple names. They only vary
-- in the condition checked so we use helper functions to associate mnemonics with
-- the conditions instead of defining each instruction at the top level.
-- TODO: We might be able to remove the aliases. It looks like the instruction encodings are the same
-- so it might suffice to find out what the decoder will pick as the canonical mnemonic.

def condition_codes : List (List String × expression bit)  := 
 [ -- Jump if above (cf = 0 and zf = 0)
   (["a", "nbe"], expression.bit_and (eq (cf : expression bit) bit_zero) (eq (zf : expression bit) bit_zero))
   -- Jump if above or equal (cf = 0)
 , (["ae", "nb", "nc"], eq (cf : expression bit) bit_zero)
   -- Jump if below (cf = 1)
 , (["b", "c", "nae"], (cf : expression bit))
   -- Jump if below or equal (cf = 1 or zf = 1)
 , (["be"], expression.bit_or (cf : expression bit) (zf : expression bit))
   -- Jump if CX is 0
 , (["cxz"], eq (cx : expression (bv 16)) 0)
   -- Jump if ECX is 0
 , (["ecxz"], eq (ecx : expression (bv 32)) 0)
   -- Jump if RCX is 0
 , (["rcxz"], eq (rcx : expression (bv 64)) 0)
   -- Jump if equal (zf = 1)
 , (["e", "z"], (zf : expression bit))
   -- Jump if greater (zf = 0 and sf = of)
 , (["g", "nle"], expression.bit_and (eq (zf : expression bit) bit_zero) (eq (sf : expression bit) (of : expression bit)))
   -- Jump if greater or equal (sf = of)
 , (["ge", "nl"], eq (sf : expression bit) (of : expression bit))
   -- Jump if less (sf ≠ of)
 , (["l", "nge"], eq (sf : expression bit) (of : expression bit))
   -- Jump if less or equal (zf = 1 or sf ≠ of)
 , (["le", "ng"], expression.bit_or (eq (expression.of_lhs zf) bit_one) (expression.of_lhs sf ≠ expression.of_lhs of))
   -- Jump if not above (cf = 1 or zf = 1)
 , (["na"], expression.bit_or (eq (expression.of_lhs cf) bit_one) (eq (expression.of_lhs zf) bit_one))
   -- Jump if not equal (zf = 0)
 , (["ne", "nz"], eq (expression.of_lhs zf) bit_zero)
   -- Jump if not overflow (of = 0)
 , (["no"], eq (expression.of_lhs of) bit_zero)
   -- Jump if not parity (pf = 0)
 , (["np", "po"], eq (expression.of_lhs pf) bit_zero)
   -- Jump if not sign (sf = 0)
 , (["ns"], eq (expression.of_lhs sf) bit_zero)
   -- Jump if overflow (of = 1)
 , (["o"], eq (expression.of_lhs of) bit_one)
   -- Jump if parity (pf = 1)
 , (["p", "pe"], eq (expression.of_lhs pf) bit_one)
   -- Jump if sign (sf = 1)
 , (["s"], eq (expression.of_lhs sf) bit_one)
 ]

------------------------------------------------------------------------
-- Jcc definition
-- Conditional jumps

def mk_jcc_instruction : String × expression bit → instruction
 | (name, cc) => definst ("j" ++ name) $ do
 instr_pat $ fun (off : imm int) =>
   let action : semantics Unit := do
    let off_bv <- eval (handleImmediateWithSignExtend off 32 64);
    let v      <- eval expression.get_rip;
    record_event (event.branch cc (add v off_bv))
   action

def mk_jcc_instruction_aliases : List String × expression bit → List instruction
 | (names, cc) => List.map (fun n => mk_jcc_instruction (n, cc)) names

-- Conditional jump instructions, some of these have multiple names. They only vary
-- in the condition checked so we use helper functions to associate mnemonics with
-- the conditions instead of defining each instruction at the top level.
-- TODO: We might be able to remove the aliases. It looks like the instruction encodings are the same
-- so it might suffice to find out what the decoder will pick as the canonical mnemonic.
def jcc_instructions : List instruction := 
  List.join $ List.map mk_jcc_instruction_aliases condition_codes

------------------------------------------------------------------------
-- ret definition
-- Return from Procedure
def retq : instruction :=
 definst "retq" $ do
   instr_pat $
    let action : semantics Unit := do
     let addr ← eval $ expression.read (bv 64) rsp;
     rsp .= coe rsp + 8;
     record_event (event.jmp addr)
    action
   ;
   instr_pat $ fun (off : expression (bv 16)) => 
    let action : semantics Unit := do
     let addr ← eval $ expression.read (bv 64) rsp;
     rsp .= coe rsp + (8 + uext off 64);
     record_event (event.jmp addr)
    action   

------------------------------------------------------------------------
-- Exported def.
-- 

def manual_instructions : List instruction :=
    [ callq
    , jmpq
    , leaveq
    , popq
    , popw
    , pushq
    , pushw
    , retq
    , syscall
    ] ++ jcc_instructions


end k_x86_semantics
end x86