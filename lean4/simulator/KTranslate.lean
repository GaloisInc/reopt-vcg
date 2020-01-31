

import KX86Semantics.Gen.Instructions
import KX86Semantics.ManualInstructions

import X86Semantics.Evaluator

import MCInst.InstParser


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
def some_reg := Sigma concrete_reg

def reg_names : List (String × some_reg) :=
  let default_reg : some_reg := Sigma.mk _ (concrete_reg.gpreg 0 gpreg_type.reg64);
  let mkOne (n : Nat) (f : Fin n -> some_reg) (name : Nat × String) : (String × some_reg) :=
      (name.snd, if H : name.fst < n then f (@Fin.mk n name.fst H) else default_reg);  
  let mk {n : Nat} (f : Fin n -> some_reg) (names : List String) : List (String × some_reg) :=
      List.map (mkOne n f) names.enum;
     mk (fun i => Sigma.mk _ (concrete_reg.gpreg i gpreg_type.reg8l)) reg.r8l_names
  ++ mk (fun i => Sigma.mk _ (concrete_reg.gpreg i gpreg_type.reg8h)) reg.r8h_names
  ++ mk (fun i => Sigma.mk _ (concrete_reg.gpreg i gpreg_type.reg16)) reg.r16_names
  ++ mk (fun i => Sigma.mk _ (concrete_reg.gpreg i gpreg_type.reg32)) reg.r32_names
  ++ mk (fun i => Sigma.mk _ (concrete_reg.gpreg i gpreg_type.reg64)) reg.r64_names
  -- FIXME: add in AVX

def reg_name_map : RBMap String some_reg (fun x y => decide (x < y)) :=
  RBMap.fromList reg_names (fun x y => decide (x < y))

def register_to_reg (r : mcinst.register) : Option some_reg :=
  reg_name_map.find r

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
  
def option_register_to_bv64
  (cfg : SystemConfig) (opt_r : Option mcinst.register) : system_m cfg.os_state (bitvec 64) := 
  match opt_r with 
  | none     => pure (bitvec.of_nat 64 0)
  | (some r) => 
    (match String.decEq r "rip" with -- FIXME: compiler bug with ite?
     | isTrue _  => do s <- get; pure s.machine_state.ip
     | isFalse _ => guard_some "option_register_to_bv64" (register_to_reg r)      
                    (fun (r' : some_reg) => match r' with
                      | (Sigma.mk (bv 64) rr) => do s <- get; pure (concrete_reg.from_state [] rr s.machine_state)
                      | _                     => throw "not a 64bit reg"
      ))


def operand_to_arg_lval (cfg : SystemConfig) (tp : type) : mcinst.operand -> system_m cfg.os_state arg_lval
  -- FIXME: check width?
  | (operand.register r) => do sgpr <- guard_some "operand_to_arg_lval register" (register_to_reg r) pure;
                               assert_types [] sgpr.fst tp;
                               pure (arg_lval.reg sgpr.snd)
  -- FIXME: check width?
  | (operand.immediate val) => throw "operand_to_arg_lval: got an immdiate"
  -- base + scale * idx + disp
  | (operand.memloc disp opt_seg opt_base scale opt_idx) => do
    n <- assert_bv [] tp;
    throw_if (Option.isSome opt_seg) "got a segment reg";
    b_v   <- option_register_to_bv64 cfg opt_base;
    idx_v <- option_register_to_bv64 cfg opt_idx;
    pure (arg_lval.memloc n (b_v + scale * idx_v + bitvec.of_int _ disp))

def operand_to_arg_value_lhs
   (cfg : SystemConfig) (tp : type) (op : mcinst.operand) : system_m cfg.os_state (arg_value []) :=
   arg_value.lval [] <$> operand_to_arg_lval cfg tp op

def operand_to_value 
   ( cfg : SystemConfig )
   (tp : type) (op : mcinst.operand) : system_m cfg.os_state (value [] tp) :=
   match op with 
     | (operand.immediate val) =>
       (match tp with
        | int    => pure val
        | _      => throw "Immediate should be a bv")
     | _ => do lval <- operand_to_arg_lval cfg tp op;
               arg_lval.to_value' cfg [] lval tp

def operand_to_arg_value_expr 
   (cfg : SystemConfig ) (tp : type) (op : mcinst.operand) : system_m cfg.os_state (arg_value []) :=
   arg_value.rval <$> operand_to_value cfg tp op

def first_comb.{u,v,w} {ε : Type u} {m : Type v → Type w}
  [MonadExcept ε m] {α : Type v} (e : ε) (f : ε -> ε -> ε) : List (m α) -> m α
  | []        => throw e
  | [x]       => x
  | (x :: xs) => catch x $ fun e1 => catch (first_comb xs) $ fun e2 => throw (f e1 e2)

/-
def test_pattern := match mov.patterns with | [x] := x | _ => sorry end

#eval possible_nat_envs test_pattern.context.bindings.reverse
-/

def make_environment_helper (cfg : SystemConfig) 
  : List binding -> List mcinst.operand -> system_m cfg.os_state (environment []) 
  | [], []              => pure []
  | (binding.one_of _ :: rest), ops => throw "Saw a one_of"
  | (binding.reg tp   :: rest), (op :: ops) =>
    annotate' "reg" $ do
      av  <- operand_to_arg_value_lhs cfg tp op;
      -- Mainly to check things are of the right form
      match av with | (arg_value.lval _ (arg_lval.reg r)) => pure () | _ => throw "Not a register";
      e   <- make_environment_helper rest ops;
      pure (av :: e)

  | (binding.addr tp   :: rest), (op :: ops) =>
    annotate' "addr" $ do
      av  <- operand_to_arg_value_lhs cfg tp op;
      -- Mainly to check things are of the right form
      match av with | (arg_value.lval _ (arg_lval.memloc _ _)) => pure () | _ => throw "Not a memloc";
      e   <- make_environment_helper rest ops;
      pure (av :: e)

  | (binding.imm tp   :: rest), (op :: ops) =>
    annotate' "imm" $ do
      -- FIXME: check that it is, in fact, an immediate
      av  <- operand_to_arg_value_expr cfg tp op;
      e   <- make_environment_helper rest ops;
      pure (av :: e)

  | (binding.lhs tp   :: rest), (op :: ops) =>
    annotate' "lhs" $ do
      av  <- operand_to_arg_value_lhs cfg tp op;
      e   <- make_environment_helper rest ops;
      pure (av :: e)
      
  | (binding.expression tp :: rest), (op :: ops) => 
    annotate' "expression" $ do 
      av  <- operand_to_arg_value_expr cfg tp op;
      e   <- make_environment_helper rest ops;
      pure (av :: e)

  | (binding.exact_reg tp r :: rest), (operand.register r' :: ops) =>
    match register_to_reg r' with
    | none => throw "Unknown register"
    | some (Sigma.mk tp' rr) => 
      if concrete_reg.nondepEq tp tp' r rr
      then do e   <- make_environment_helper rest ops;
              -- value here can be anything
              pure (arg_value.lval [] (arg_lval.reg r) :: e)
      else throw "Register mismatch"
    
  | _, _ => throw "binding/operand mismatch"

def make_environment (cfg : SystemConfig) (bindings : List binding) (ops : List mcinst.operand) 
  : system_m cfg.os_state (Sigma environment) :=
  (do e <- make_environment_helper cfg bindings ops; pure (Sigma.mk [] e))

def instantiate_pattern (cfg : SystemConfig) (inst : x86.instruction) (i : mcinst.instruction) 
  : system_m cfg.os_state ((Sigma environment) × x86.pattern) :=
  first_comb "instantiate_pattern: no patterns" (fun l r => r) -- l ++ ", " ++ r)
              (List.map (fun (p : x86.pattern) => do e <- make_environment cfg p.context.bindings.reverse i.args; pure (e, p)) inst.patterns)

-- def eval_simple_instruction (s : instruction) (i : decodex86.instruction) : evaluator environment :=
--   match s.patterns with
--   | [p] => do match_context p.context.bindings.reverse i.operands;
--               s <- get;
--               pure s.environment
--   | _   => throw "not a simple instruction"
--   end

def instruction_map : RBMap String x86.instruction (fun x y => decide (x < y)) :=
  RBMap.fromList (List.map (fun (i : x86.instruction) => (i.mnemonic, i)) 
                 (k_x86_semantics.all_instructions ++ k_x86_semantics.manual_instructions)) (fun x y => decide (x < y))

def eval_instruction' ( cfg : SystemConfig ) (i : mcinst.instruction) 
  : system_m cfg.os_state Unit :=
  match instruction_map.find i.mnemonic with               
  | none        => throw ("Unknown instruction: " ++ i.mnemonic)
  | (some inst) => do (Sigma.mk nenv env, p) <- annotate' "pattern" (instantiate_pattern cfg inst i);
                      annotate' "pattern.eval" (pattern.eval cfg nenv p env)

def eval_instruction ( cfg : SystemConfig ) (s : system_state cfg.os_state) (i : mcinst.instruction) 
    : IO (Except String (system_state cfg.os_state)) := 
    do r <- system_m.run (eval_instruction' cfg i) s;
       pure ((fun (v : Unit × system_state cfg.os_state) => v.snd) <$> r)

end mcinst
end x86

