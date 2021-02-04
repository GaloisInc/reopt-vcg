

import KX86Semantics.Gen.Instructions
import KX86Semantics.ManualInstructions

import X86Semantics.BackendAPI
import X86Semantics.Evaluator

import MCInst.InstParser

open Std (RBMap)

-- namespace x86
-- namespace k_x86_semantics

-- def all_instructions : List instruction := []

-- end k_x86_semantics
-- end x86

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

namespace x86

namespace mcinst

@[reducible]
def some_gpr := Sigma (fun (tp : gpreg_type) => concrete_reg (bv tp.width))

-- @[reducible]
-- def some_reg := Sigma concrete_reg

def reg_names : List (String × some_gpr) :=
  let default_reg : some_gpr := Sigma.mk _ (concrete_reg.gpreg 0 gpreg_type.reg64);
  let mkOne (n : Nat) (f : Fin n -> some_gpr) (name : Nat × String) : (String × some_gpr) :=
      (name.snd, if H : name.fst < n then f (@Fin.mk n name.fst H) else default_reg);  
  let mk {n : Nat} (f : Fin n -> some_gpr) (names : List String) : List (String × some_gpr) :=
      List.map (mkOne n f) names.enum;
     mk (fun i => Sigma.mk _ (concrete_reg.gpreg i gpreg_type.reg8l)) reg.r8l_names
  ++ mk (fun i => Sigma.mk _ (concrete_reg.gpreg i gpreg_type.reg8h)) reg.r8h_names
  ++ mk (fun i => Sigma.mk _ (concrete_reg.gpreg i gpreg_type.reg16)) reg.r16_names
  ++ mk (fun i => Sigma.mk _ (concrete_reg.gpreg i gpreg_type.reg32)) reg.r32_names
  ++ mk (fun i => Sigma.mk _ (concrete_reg.gpreg i gpreg_type.reg64)) reg.r64_names
  -- FIXME: add in AVX

def reg_name_map : RBMap String some_gpr (fun x y => decide (x < y)) :=
  Std.RBMap.fromList reg_names (fun x y => decide (x < y))

def register_to_reg (r : mcinst.register) : Option some_gpr :=
  reg_name_map.find? r

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

variable (backend : Backend)

def option_register_to_bv64 (opt_r : Option mcinst.register) : M backend (backend.s_bv 64) := 
  match opt_r with 
  | none     => pure (backend.s_bv_imm 64 0)
  | (some r) => 
    (match String.decEq r "rip" with -- FIXME: compiler bug with ite?
     | isTrue _  => backend.s_get_ip
     | isFalse _ => guard_some "option_register_to_bv64" (register_to_reg r)
                    (fun (r' : some_gpr) =>
                      match r' with 
                      | (Sigma.mk gpreg_type.reg64 rr) => concrete_reg.from_state rr
                      | _                              => throw "not a 64bit reg"
      ))

def operand_to_arg_lval (tp : type) : mcinst.operand -> M backend (@arg_lval backend)
  -- FIXME: check width?
  | (operand.register r) => do 
    let sgpr <- guard_some "operand_to_arg_lval register" (register_to_reg r) pure;
    assert_types (bv sgpr.fst.width) tp;
    pure (arg_lval.reg sgpr.snd)
  -- FIXME: check width?
  | (operand.immediate val) => throw "operand_to_arg_lval: got an immdiate"
  -- base + scale * idx + disp
  | (operand.memloc disp opt_seg opt_base scale opt_idx) => do
    let n <- assert_bv tp;
    throw_if (Option.isSome opt_seg) "got a segment reg";
    let b_v   <- option_register_to_bv64 backend opt_base;
    let idx_v <- option_register_to_bv64 backend opt_idx;
    pure (arg_lval.memloc n (backend.s_bvadd _ b_v
                              (backend.s_bvadd _ (backend.s_bvmul _ (backend.s_bv_imm _ scale) idx_v)
                              (backend.s_bv_imm_int _ disp))))
-- (b_v + scale * idx_v + bitvec.of_int _ disp))

def operand_to_arg_value_lhs
   (tp : type) (op : mcinst.operand) : M backend (@arg_value backend) :=
   arg_value.lval <$> operand_to_arg_lval backend tp op

def operand_to_value (tp : type) (op : mcinst.operand) : M backend (@value backend tp) :=
   match op with 
     | (operand.immediate val) =>
       (match tp with
        | int    => pure val
        | _      => throw "Immediate should be an int")
     | _ => do let lval <- operand_to_arg_lval backend tp op;
               arg_lval.to_value' lval tp

def operand_to_arg_value_expr 
   (tp : type) (op : mcinst.operand) : M backend (@arg_value backend) :=
   arg_value.rval <$> operand_to_value backend tp op

def first_comb.{u,v,w} {ε : Type u} {m : Type v → Type w}
  [MonadExcept ε m] {α : Type v} (e : ε) (f : ε -> ε -> ε) : List (m α) -> m α
  | []        => throw e
  | [x]       => x
  | (x :: xs) => tryCatch x (fun e1 => tryCatch (first_comb e f xs) (fun e2 => throw (f e1 e2)))

/-
def test_pattern := match mov.patterns with | [x] := x | _ => sorry end

#eval possible_nat_envs test_pattern.context.bindings.reverse
-/

def make_environment_helper : List binding -> List mcinst.operand -> M backend (@environment backend) 
  | [], []              => pure []
  | (binding.reg tp   :: rest), (op :: ops) =>
    annotate' "reg" $ do
      let av  <- operand_to_arg_value_lhs backend tp op;
      -- Mainly to check things are of the right form
      match av with | (arg_value.lval (arg_lval.reg r)) => pure () | _ => throw "Not a register";
      let e   <- make_environment_helper rest ops;
      pure (av :: e)

  | (binding.addr tp   :: rest), (op :: ops) =>
    annotate' "addr" $ do
      let av  <- operand_to_arg_value_lhs backend tp op;
      -- Mainly to check things are of the right form
      match av with | (arg_value.lval (arg_lval.memloc _ _)) => pure () | _ => throw "Not a memloc";
      let e   <- make_environment_helper rest ops;
      pure (av :: e)

  | (binding.imm tp   :: rest), (op :: ops) =>
    annotate' "imm" $ do
      -- FIXME: check that it is, in fact, an immediate
      let av  <- operand_to_arg_value_expr backend tp op;
      let e   <- make_environment_helper rest ops;
      pure (av :: e)

  | (binding.lhs tp   :: rest), (op :: ops) =>
    annotate' "lhs" $ do
      let av  <- operand_to_arg_value_lhs backend tp op;
      let e   <- make_environment_helper rest ops;
      pure (av :: e)
      
  | (binding.expression tp :: rest), (op :: ops) => 
    annotate' "expression" $ do 
      let av  <- operand_to_arg_value_expr backend tp op;
      let e   <- make_environment_helper rest ops;
      pure (av :: e)

  | (binding.exact_reg tp r :: rest), (operand.register r' :: ops) =>
    match register_to_reg r' with
    | none => throw "Unknown register"
    | some (Sigma.mk tp' rr) => 
      if concrete_reg.nondepEq tp (bv tp'.width) r rr
      then do let e   <- make_environment_helper rest ops;
              -- value here can be anything
              pure (arg_value.lval (arg_lval.reg r) :: e)
      else throw "Register mismatch"    
  | _, _ => throw "binding/operand mismatch"

def instantiate_pattern (inst : x86.instruction) (i : mcinst.instruction) 
  : M backend (@environment backend × x86.pattern) :=
  first_comb "instantiate_pattern: no patterns" (fun l r => r) -- l ++ ", " ++ r)
              (List.map (fun (p : x86.pattern) => 
               do let e <- make_environment_helper backend p.context.bindings.reverse i.args;
                  pure (e, p)) 
              inst.patterns)

def instruction_map : RBMap String x86.instruction (fun x y => decide (x < y)) :=
  Std.RBMap.fromList (List.map (fun (i : x86.instruction) => (i.mnemonic, i)) 
                     (k_x86_semantics.all_instructions ++ k_x86_semantics.manual_instructions)) (fun x y => decide (x < y))

def eval_instruction (i : mcinst.instruction) : M backend Unit :=
  match instruction_map.find? i.mnemonic with               
  | none        => throw ("Unknown instruction: " ++ reprStr i)
  | (some inst) => do let (env, p) <- annotate' ("pattern " ++ reprStr i) (instantiate_pattern backend inst i);
                      annotate' "pattern.eval" (pattern.eval p env)

end Backend

end mcinst
end x86

