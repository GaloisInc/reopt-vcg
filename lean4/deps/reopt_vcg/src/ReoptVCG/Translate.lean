

import X86Semantics.Instructions
import X86Semantics.BackendAPI
import X86Semantics.Evaluator

import DecodeX86.DecodeX86



open mc_semantics
open mc_semantics.type

-- lemma {u} find_index_lt {α : Type u} (p : α -> Prop) [decidable_pred p] : Π(ls : list α), list.find_index p ls ≤ ls.length := 
--   begin
--     intros,
--     induction ls,
--     { simp [list.find_index] },
--     { simp [list.find_index],
--       by_cases (p ls_hd), 
--         { simp [h] },
--         { simp [h, nat.one_add], apply nat.succ_le_succ, exact ls_ih }
--     }
--   end

-- lemma {u} index_of_lt {α : Type u} [decidable_eq α] (ls : list α) (x : α) 
--   : list.index_of x ls ≤ ls.length := by apply find_index_lt

namespace List

universe u

protected
def indexOfAux {α : Type u} [DecidableEq α] (v : α) : Nat -> List α -> Nat
  | n, [] => n
  | n, (x :: xs) => if x = v then n else indexOfAux (n + 1) xs

def indexOf {α : Type u} [DecidableEq α] (xs : List α) (v : α) : Nat := List.indexOfAux v 0 xs

end List

namespace x86

@[reducible]
def some_gpr := Sigma (fun (tp : gpreg_type) => concrete_reg (bv tp.width))

def register_to_reg (r : decodex86.register) : Option some_gpr :=
  let idx := reg.r64_names.indexOf r.top;
  if H : idx = reg.r64_names.length 
  then none
  else let prf : idx < 16 := I_am_really_sorry _;
       let idx' := @Fin.mk 16 idx prf; -- (begin
           -- destruct (lt_or_eq_of_le (index_of_lt reg.r64_names r.top)); intros Hle,
           -- exact Hle,
           -- contradiction
           -- end)
       let mk : ∀(tp : gpreg_type), Option some_gpr
                 := fun (tp : gpreg_type) => some ⟨tp, concrete_reg.gpreg idx' tp⟩;  
       match (r.width, r.offset) with 
         | (8, 0)  => mk gpreg_type.reg8l
         | (8, 8)  => mk gpreg_type.reg8h
         | (16, 0) => mk gpreg_type.reg16
         | (32, 0) => mk gpreg_type.reg32
         | (0, 0)  => mk gpreg_type.reg64 -- 0 0 means full reg.     
         | _       => none

open decodex86

def throw_if {m} {ε} [Monad m] [MonadExcept ε m] (P : Prop) [Decidable P] (what : ε) : m Unit :=
  if P then throw what else pure ()

-- instance {α : Type} : decidable_pred (@option.is_none α) := 
--   begin
--     unfold decidable_pred, 
--     intros,
--     cases a,
--     { simp [is_none], apply is_true, constructor},
--     { simp [is_none], apply is_false, simp}
--   end

-- instance is_some_decidable {α : Type} : decidable_pred (@option.is_some α) := 
--   begin
--     unfold decidable_pred, 
--     intros,
--     cases a,
--     { simp [is_some], apply is_false, simp},
--     { simp [is_some], apply is_true, constructor}
--   end

def guard_some {m} [Monad m] [MonadExcept String m] {α β : Type} (reason : String) (x : Option α) (f : α -> m β) : m β :=
  match x with 
  | none     => throw (String.append "guard_some: none: " reason)
  | (some y) => f y


section Backend

variables (backend : Backend)

def option_register_to_bv64 (opt_r : Option decodex86.register) : M backend (backend.s_bv 64) := 
  match opt_r with 
  | none     => pure (backend.s_bv_imm 64 0)
  | (some r) => 
    (match String.decEq r.top "rip" with -- FIXME: compiler bug with ite?
     | isTrue _  => backend.s_get_ip
     | isFalse _ => guard_some "option_register_to_bv64" (register_to_reg r)      
                    (fun (r' : some_gpr) =>
                      match r' with 
                      | (Sigma.mk gpreg_type.reg64 rr) => concrete_reg.from_state rr
                      | _                              => throw "not a 64bit reg"
      ))


def operand_to_arg_lval
    (tp : type) (otp : decodex86.operand_type) : decodex86.operand_value 
    -> M backend (@arg_lval backend)
  -- FIXME: check width?
  | (operand_value.register r) => do 
    sgpr <- guard_some "operand_to_arg_lval register" (register_to_reg r) pure;
    assert_types (bv sgpr.fst.width) tp;
    pure (arg_lval.reg sgpr.snd)

  -- FIXME: check width?
  | (operand_value.segment opt_r r) => do
    throw_if (Option.isSome opt_r) "got a segment reg";
    -- FIXME: clag
    sgpr <- guard_some "operand_to_arg_value_lhs register" (register_to_reg r) pure;
    assert_types (bv sgpr.fst.width) tp;
    pure (arg_lval.reg sgpr.snd)
  | (operand_value.immediate nbytes val) => throw "operand_to_arg_lval: got an immdiate"
  -- FIXME: we use ip out of the state, we could use the value encoded in the decoded instruction 
  | (operand_value.rel_immediate next_addr nbytes val) => throw "operand_to_arg_lval: got an immdeiate"
  -- base + scale * idx + disp
  | (operand_value.memloc opt_seg opt_base scale opt_idx disp) => do
    n <- match otp with | (operand_type.mem n) => pure n | other => throw "memloc not of mem type";
    assert_types (bv n) tp;
    throw_if (Option.isSome opt_seg) "got a segment reg";
    b_v   <- option_register_to_bv64 backend opt_base;
    idx_v <- option_register_to_bv64 backend opt_idx;
    pure (arg_lval.memloc n (backend.s_bvadd _ b_v
                              (backend.s_bvadd _ (backend.s_bvmul _ (backend.s_bv_imm _ scale) idx_v)
                              (backend.s_bv_imm _ disp))))

def operand_to_arg_value_lhs
   (tp : type) (op : decodex86.operand) : M backend (@arg_value backend) :=
   arg_value.lval <$> operand_to_arg_lval backend tp op.type op.value

def nat_to_signed_bitvec (val : Nat) (nbytes_in : Nat) (n : Nat) : backend.s_bv n :=
  backend.s_sext _ n (backend.s_bv_imm (8 * nbytes_in) val)

def operand_to_value    
   (tp : type) (op : decodex86.operand) : M backend (@value backend tp) :=
   match op.value with 
     | (operand_value.immediate nbytes val) => do
     
     -- FIXME: rather than failing here, we will sign extend/truncate.  This may be the wrong approach.
     -- We could also extend operand_type
       (match tp with
       | (bv e) => pure (nat_to_signed_bitvec backend val nbytes e)
       | _      => throw "Immediate should be a bv")

     -- FIXME: we use ip out of the state, we could use the value encoded in the decoded instruction 
     | (operand_value.rel_immediate next_addr nbytes val) => do
       -- checks for width = 64 bit, basically
       -- @value.type_check nenv m _ _ (bv 64) (s.ip + nat_to_signed_bitvec val nbytes 64) tp
       ip <- backend.s_get_ip;
       value.type_check (bv 64)
                        (backend.s_bvadd _ ip (nat_to_signed_bitvec backend val nbytes 64))
                        tp
     | _ => do lval <- operand_to_arg_lval backend tp op.type op.value;
               arg_lval.to_value' lval tp

   
def operand_to_arg_value_expr    
   (tp : type) (op : decodex86.operand) : M backend (@arg_value backend) :=
   arg_value.rval <$> operand_to_value backend tp op

def first_comb.{u,v,w} {ε : Type u} {m : Type v → Type w}
  [MonadExcept ε m] {α : Type v} (e : ε) (f : ε -> ε -> ε) : List (m α) -> m α
  | []        => throw e
  | [x]       => x
  | (x :: xs) => catch x $ fun e1 => catch (first_comb xs) $ fun e2 => throw (f e1 e2)

/-
def test_pattern := match mov.patterns with | [x] := x | _ => sorry end

#eval possible_nat_envs test_pattern.context.bindings.reverse
-/

def make_environment_helper 
  : List binding -> List decodex86.operand -> M backend (@environment backend)
  | [], []              => pure []
  | (binding.reg tp   :: rest), (op :: ops) =>
    annotate' "reg" $ do
      av  <- operand_to_arg_value_lhs backend tp op;
      -- Mainly to check things are of the right form
      match av with | (arg_value.lval (arg_lval.reg r)) => pure () | _ => throw "Not a register";
      e   <- make_environment_helper rest ops;
      pure (av :: e)

  | (binding.addr tp   :: rest), (op :: ops)  =>
    annotate' "addr" $ do
      av  <- operand_to_arg_value_lhs backend tp op;
      -- Mainly to check things are of the right form
      match av with | (arg_value.lval (arg_lval.memloc _ _)) => pure () | _ => throw "Not a memloc";
      e   <- make_environment_helper rest ops;
      pure (av :: e)

  | (binding.imm tp   :: rest), (op :: ops) =>
    annotate' "imm" $ do
      -- FIXME: check that it is, in fact, an immediate
      av  <- operand_to_arg_value_expr backend tp op;
      e   <- make_environment_helper rest ops;
      pure (av :: e)

  | (binding.lhs tp   :: rest), (op :: ops) =>
    annotate' "lhs" $ do
      av  <- operand_to_arg_value_lhs backend tp op;
      e   <- make_environment_helper rest ops;
      pure (av :: e)
      
  | (binding.expression tp :: rest), (op :: ops) => 
    annotate' "expression" $ do 
      av  <- operand_to_arg_value_expr backend tp op;
      e   <- make_environment_helper rest ops;
      pure (av :: e)
  | _, _ => throw "binding/operand mismatch"

/-
inductive binding
| one_of : list nat → binding
| reg  : type → binding
| addr : type → binding
| imm  : type → binding
| lhs  : type → binding
| expression : type → binding
-/

def instantiate_pattern  (inst : instruction) (i : decodex86.instruction) 
  : M backend (@environment backend × x86.pattern) :=
  first_comb "instantiate_pattern: no patterns" (fun l r => r) -- l ++ ", " ++ r)
              (List.map (fun (p : x86.pattern) => 
                do e <- make_environment_helper backend p.context.bindings.reverse i.operands;
                   pure (e, p)) 
              inst.patterns)

def instruction_family (inst : decodex86.instruction) : String :=
  let (pfx, rest) := List.span Char.isUpper inst.mnemonic.toList;
  (List.map Char.toLower pfx).asString

def instruction_map : Std.RBMap String instruction (fun x y => decide (x < y)) :=
  Std.RBMap.fromList (List.map (fun (i : instruction) => (i.mnemonic, i)) all_instructions) (fun x y => decide (x < y))

def eval_instruction (i : decodex86.instruction) : M backend Unit :=
  match instruction_map.find? (instruction_family i) with               
  | none        => throw ("Unknown instruction: " ++ i.mnemonic)
  | (some inst) => do (env, p) <- annotate' "pattern" (instantiate_pattern backend inst i);
                      annotate' "pattern.eval" (pattern.eval p env)
  
/- testing -/
-- def get_sexp : String -> sexp := fun st => 
--     match sexp.from_string st with
--       | (sum.inr s) => s
--       | _           => sexp.list []
--     end

-- def string_to_instruction (s : String) : Option decodex86.instruction :=
--   decodex86.exec_parser decodex86.parser.instructionp (get_sexp s)
  
-- def go (s : String) : String := 
--   match string_to_instruction s with 
--   | none     => "No parse"
--   | (some i) => repr i.operands
--   end

-- namespace except

-- def to_sum {a} {b} : except a b -> sum a b 
--   | (except.error e) => sum.inl e
--   | (except.ok v)    => sum.inr v

-- end except

-- def go2 (s : String) (si : instruction) : String := 
--   match string_to_instruction s with 
--   | none     => "No parse"
--   | (some i) => match ((eval_simple_instruction si i).run evaluator_state.empty) with
--                 | (except.error e)   => "error: " ++ e
--                 | (except.ok (e, _)) => has_repr.repr e
--                 end
--   end

-- def run_get_rax (s : String) : String :=
--   match string_to_instruction s with 
--   | none     => "No parse"
--   | (some i) => match (eval_instruction machine_state.empty i) with
--                 | (except.error e) => "error: " ++ e
--                 | (except.ok    s) => s.print_regs -- has_repr.repr (s.get_gpreg 0)
--                 end
--   end

-- #eval instruction_family <$> string_to_instruction "(instruction MOV32ri (register rax eax 32 0) (immediate 4 1))"

-- #eval run_get_rax "(instruction MOV64ri32 (other (register rax rax 0 0)) (other (immediate 4 4294967295)))"
-- #eval run_get_rax "(instruction MOV32mi (i32mem (memloc no-register (register rax rax 0 0) 1 no-register 0)) (i32imm (immediate 4 65535)))"
end Backend

end x86

