
import X86Semantics.Common

import ReoptVCG.VCGBackend
import ReoptVCG.Annotations
import ReoptVCG.Types

namespace x86
namespace vcg

open ReoptVCG (MemoryAnn)

structure Semantics :=
  (instruction : Type)
  (instruction_size : instruction -> Nat)
  (decode      : Nat -> Sum String instruction)
  (eval        : forall (backend : Backend), instruction -> backend.monad Unit)


-- We can't stick the above in Context as it is in Type 1
open mc_semantics.type

def mkBackendFuns ( sem : Semantics ) ( fpOps  : SupportedFPOps ) : InstructionEventsFun × GetRegisterFun :=
  let backend := mkBackend fpOps
  let instructionEvents := fun
    -- ^ SMT operations over floating point
    ( evtMap : Std.RBMap Nat MemoryAnn Ord.compare )
    -- ^ Map from addresses to annotations of events on that address.
    ( s : RegState )
    -- ^ Initial values for registers
    ( idGen : IdGen)
    -- ^ Used to generate unique/fresh identifiers for SMT terms.
    ( ip : Nat ) =>
    -- ^ Location to explore
    let inst := sem.decode ip;
    match inst with 
    | (Sum.inl _) => throw "Unknown byte"
    | (Sum.inr i) => do
         -- set ip of next instruction, used for getting ip-relative addrs.
         let nextIP := ip + sem.instruction_size i;
         let s'  := { s with ip := Smt.bvimm _ nextIP };
         let evt := evtMap.find? ip;
         let r := (sem.eval backend i).run
                  { idGen := idGen, eventInfo := evt, revEvents := [], fpOps := fpOps }
                  s';
         match r with
         | Except.ok ((_, s''), os'') =>
               let fAndE := Event.FetchAndExecuteEvent s'';
               Except.ok (List.reverse (fAndE :: os''.revEvents), os''.idGen, sem.instruction_size i)
         | Except.error err => Except.error err -- (err ++ " " ++ repr i)
  
  let get_bvreg := fun (s : RegState) {n : Nat} (r : concrete_reg (bv n)) =>
    match n, r with
    | _, concrete_reg.gpreg  idx rtp => @reg.project backend rtp (s.get_gpreg idx)
    | _, concrete_reg.avxreg idx atp => @reg.avx_project backend atp (s.get_avxreg idx)

  (instructionEvents, get_bvreg)


end vcg
end x86
