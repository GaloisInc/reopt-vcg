
-- import system.io
import Galois.Init.Io
-- FIXME!! this is from the simulator
import Main.Translate
import X86Semantics.SymbolicBackend
import DecodeX86.DecodeX86
import SmtLib.Smt

namespace x86
namespace symbolic

def throwS {a : Type} {m : Type -> Type} [MonadIO m] (e : String) : m a := 
  monadLift (throw (IO.userError e) : IO a)
 
-- def evaluate_one (s : machine_state) : (Nat × sum unknown_byte instruction) -> except String machine_state
--   | (n, sum.inl err)  => throw "Got an unknown byte"
--   | (n, sum.inr inst) := eval_instruction {s with ip => s.ip + bitvec.of_nat _ n} inst

-- def lift_eval {α : Type *} |  evaluator α) : io a

-- def dump_state (s : system_state linux.x86_64.os_state) : IO Unit := do
--   let line := s.ip.pp_hex ++ ": " ++ s.print_regs ++ " " ++ s.print_set_flags;
--   IO.println line

def bytesToByteArray (xs : List String) : ByteArray :=
  let bs := List.map (fun x => UInt8.ofNat ((String.toNat? x).getD 0)) xs;
  bs.toByteArray

def doit (bs : List String) : IO Unit := do
  let text_bytes := bytesToByteArray bs;
  let d := decodex86.mk_decoder text_bytes 0;
  let ((init_s, stdlib), (idGen', init_script)) :=
      Smt.runSmtM Smt.IdGen.empty
        (do init_s <- machine_state.declare_const;
            stdlib <- StdLib.make;
            pure (init_s, stdlib));
  IO.println "Prelude:";
  _ <- init_script.mapM (fun c => IO.println (toString (toSExpr c)));
  IO.println "\nInstruction:";
  
  let inst := decodex86.decode d 0;
  match inst with 
  | (Sum.inl b) => throwS "Unknown byte"
  | (Sum.inr i) => do
       -- let s'  := {s with ip := s.ip + bitvec.of_nat _ i.nbytes };
       -- let os' := {os with current_ip := s.ip};
       -- IO.println (repr i);
       let r := (eval_instruction (symbolicBackend stdlib) i).run            
                { os_state.empty with idGen := idGen' }
                init_s;
       match r with
       | Except.ok ((_, s''), os'') => do  
         _ <- os''.trace.reverse.mapM (fun (e : Event) => IO.println (repr e));
         IO.println (machine_state.print_regs s'');
         pure ()
       | Except.error e => throwS ("Eval failed: " ++ e)

end symbolic
end x86
    
def main (xs : List String) : IO UInt32 := 
    do x86.symbolic.doit xs; pure 0
