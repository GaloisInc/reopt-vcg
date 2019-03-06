
import .instructions
import .evaluator
import decodex86
import tactic.find

open mc_semantics
open mc_semantics.type

lemma {u} find_index_lt {α : Type u} (p : α -> Prop) [decidable_pred p] : Π(ls : list α), list.find_index p ls ≤ ls.length := 
  begin
    intros,
    induction ls,
    { simp [list.find_index] },
    { simp [list.find_index],
      by_cases (p ls_hd), 
        { simp [h] },
        { simp [h, nat.one_add], apply nat.succ_le_succ, exact ls_ih }
    }
  end

lemma {u} index_of_lt {α : Type u} [decidable_eq α] (ls : list α) (x : α) 
  : list.index_of x ls ≤ ls.length := by apply find_index_lt

namespace x86

@[reducible]
def some_gpr := sigma (λ(tp : gpreg_type), reg (bv tp.width))

def register_to_reg (r : decodex86.register) : option some_gpr :=
  let idx := reg.r64_names.index_of r.top in
  if H : idx = reg.r64_names.length 
  then none
  else let idx' := @fin.mk 16 idx (begin
           destruct (lt_or_eq_of_le (index_of_lt reg.r64_names r.top)); intros Hle,
           exact Hle,
           contradiction
           end)
       in let mk : Π(tp : gpreg_type), option some_gpr
                 := λ(tp : gpreg_type), some ⟨tp, reg.concrete_gpreg idx' tp⟩
       in
       match (r.width, r.offset) with 
         | (8, 0)  := mk gpreg_type.reg8l
         | (8, 8)  := mk gpreg_type.reg8h
         | (16, 0) := mk gpreg_type.reg16
         | (32, 0) := mk gpreg_type.reg32
         | (0, 0)  := mk gpreg_type.reg64 -- 0 0 means full reg.     
         | _      := none
       end

open decodex86

def throw_if {m} {ε} [monad m] [monad_except ε m] (P : Prop) [decidable P] (what : ε) : m unit :=
  if P then throw what else return ()

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

def guard_some {m} [monad m] [monad_except string m] {α β : Type} (reason : string) (x : option α) (f : α -> m β) : m β :=
  match x with 
  | none := throw (string.append "guard_some: none: " reason)
  | (some y) := f y
  end
  
def option_register_to_bv64 {m} [monad m] [monad_except string m] 
  (nenv : nat_env) (s : machine_state)
  (opt_r : option decodex86.register) : m (bitvec 64) := 
  match opt_r with 
  | none := return (bitvec.of_nat 64 0)
  | (some r) := guard_some "option_register_to_bv64" (register_to_reg r)      
    (λ(r' : some_gpr),
      match r' with 
      | (sigma.mk gpreg_type.reg64 rr) := return (reg.from_state nenv rr s)
      | _                              := throw "not a 64bit reg"
      end) 
  end

def assert_types {m} [monad m] [monad_except string m] 
  (nenv : nat_env) 
  (t1 t2 : type) : m unit :=
  if eval_type nenv t1 = eval_type nenv t2
  then return () 
  else throw $ "Type mismatch: " ++ t1.pp ++ " and " ++ t2.pp ++ " in " ++ repr nenv

def assert_bv {m} [monad m] [monad_except string m] (nenv : nat_env) (tp : type) : m ℕ :=
  match tp with
  | (bv e) := return (nat_expr.eval_default nenv e)
  | _      := throw "Not a bitvecor"
  end             

def operand_to_arg_lval {m} [monad m] [monad_except string m] 
    (nenv : nat_env) (s : machine_state) 
    (tp : type) : decodex86.operand -> m arg_lval
  -- FIXME: check width?
  | (operand.register r) := do sgpr <- guard_some "operand_to_arg_lhs register" (register_to_reg r) return,
                               assert_types nenv (bv sgpr.fst.width) tp,
                               return (arg_lval.reg sgpr.snd)
  -- FIXME: check width?
  | (operand.segment opt_r r) := do
    throw_if (option.is_some opt_r) "got a segment reg",
    -- FIXME: clag
    sgpr <- guard_some "operand_to_arg_value_lhs register" (register_to_reg r) return,
    assert_types nenv (bv sgpr.fst.width) tp,
    return (arg_lval.reg sgpr.snd)
  | (operand.immediate nbytes val) := throw "operand_to_arg_lval: got an immdiate"
  -- FIXME: we use ip out of the state, we could use the value encoded in the decoded instruction 
  | (operand.rel_immediate next_addr nbytes val) := throw "operand_to_arg_lval: got an immdeiate"
  -- base + scale * idx + disp
  | (operand.memloc opt_seg opt_base scale opt_idx disp) := do
    throw_if (option.is_some opt_seg) "got a segment reg",
    width <- assert_bv nenv tp,
    b_v   <- option_register_to_bv64 nenv s opt_base,
    idx_v <- option_register_to_bv64 nenv s opt_idx,
    return (arg_lval.memloc width (b_v + scale * idx_v + disp))

def operand_to_arg_value_lhs {m} [monad m] [monad_except string m] 
   (nenv : nat_env) (s : machine_state)
   (tp : type) (op : decodex86.operand) : m (arg_value nenv) :=
   arg_value.lval nenv <$> operand_to_arg_lval nenv s tp op

def operand_to_value {m} [monad m] [monad_except string m] 
   (nenv : nat_env) (s : machine_state)
   (tp : type) : decodex86.operand -> m (value nenv tp)
  | (operand.immediate nbytes val) :=
    @value.type_check nenv m _ _ (bv (8 * nbytes)) (bitvec.of_nat _ val) tp
  -- FIXME: we use ip out of the state, we could use the value encoded in the decoded instruction 
  | (operand.rel_immediate next_addr nbytes val) := do
    -- checks for width = 64 bit, basically
    @value.type_check nenv m _ _ (bv 64) (s.ip + val) tp
  | op := do lval <- operand_to_arg_lval nenv s tp op,
             arg_lval.to_value' nenv s lval tp

def operand_to_arg_value_expr {m} [monad m] [monad_except string m] 
   (nenv : nat_env) (s : machine_state)
   (tp : type) (op : decodex86.operand) : m (arg_value nenv) :=
   arg_value.rval <$> operand_to_value nenv s tp op

def operand_nbits : decodex86.operand -> option ℕ
  | (operand.register r) := some (if r.width = 0 then 64 else r.width) -- FIXME: maybe fix this earlier?
  | (operand.segment opt_r r) := some (if r.width = 0 then 64 else r.width)
  | (operand.immediate nbytes val) := some (8 * nbytes)
  | (operand.rel_immediate next_addr nbytes val) := some (8 * nbytes)
  | (operand.memloc opt_seg opt_base scale opt_idx disp) := none

def instruction_operand_width (os : list decodex86.operand) : option ℕ :=
  match list.filter_map operand_nbits os with
  | [] := none
  | (x :: xs) := if xs.all (λy, y = x) then some x else none
  end

-- Constructs an environment which is natv w, lhs l, expr e, and sets it in the state
-- def operands_to_env_wle : list decodex86.operand -> evaluator (ℕ × environment)
--   | [l, e] := do width <- guard_some "instruction_env_w_l_e" (instruction_operand_width [l, e]) return,
--                  l_a   <- operand_to_arg_value_lhs width l,
--                  e_a   <- operand_to_arg_value_expr width e,
--                  return (width, [arg_value.natv width, l_a, e_a])
--   | _      := throw "Expecting exactly 2 operands"

-- assumes ip has already been set.
-- def eval_simple_instruction_wle  (s : instruction) (i : decodex86.instruction) : evaluator unit := do
--   (width, env) <- operands_to_env_wle i.operands,
--   match s.patterns with
--   | [p] := p.eval env
--   | _   := throw "not a simple instruction"
--   end

def {u v w} first_comb {ε : Type u} {m : Type v → Type w}
  [monad_except ε m] {α : Type v} (e : ε) (f : ε -> ε -> ε) : list (m α) -> m α
  | []        := throw e
  | [x]       := x
  | (x :: xs) := catch x $ λe1, catch (first_comb xs) $ λe2, throw (f e1 e2)

-- Inside the list monad here
def possible_nat_envs : list binding -> list nat_env
  | []                        := [[]]
  | (binding.one_of ns :: xs) := do n <- ns, e <- possible_nat_envs xs, return (some n :: e)
  | (_ :: xs)                 := do e <- possible_nat_envs xs, return (none :: e)

/-
def test_pattern := match mov.patterns with | [x] := x | _ := sorry end

#eval possible_nat_envs test_pattern.context.bindings.reverse
-/

def make_environment_helper (nenv : nat_env) (s : machine_state) 
  : list binding -> list decodex86.operand -> nat_env -> except string (environment nenv) 
  | [] [] _              := return []
  | (binding.one_of _ :: rest) ops (some n :: ns) := do e <- make_environment_helper rest ops ns,
                                                        return (arg_value.natv nenv n :: e)
  | (binding.lhs tp   :: rest) (op :: ops) (_ :: ns) :=
    annotate' "lhs" $ do
      av  <- operand_to_arg_value_lhs nenv s tp op,
      e   <- make_environment_helper rest ops ns,
      return (av :: e)
      
  | (binding.expression tp :: rest) (op :: ops) (_ :: ns) := 
    annotate "expression" $ do 
      av  <- operand_to_arg_value_expr nenv s tp op,
      e   <- make_environment_helper rest ops ns,
      return (av :: e)
  | _ _ _ := throw "binding/operand mismatch"

def make_environment (s : machine_state) (bindings : list binding) (ops : list decodex86.operand) 
  : except string (sigma environment) :=
  first_comb "make_environment: no patterns" (λl r, l ++ ", " ++ r)
             (list.map (λnenv, do e <- make_environment_helper nenv s bindings ops nenv, return (sigma.mk nenv e)) (possible_nat_envs bindings))

def instantiate_pattern (s : machine_state) (inst : instruction) (i : decodex86.instruction) 
  : except string ((sigma environment) × x86.pattern) :=
  first_comb "instantiate_pattern: no patterns" (λl r, l ++ ", " ++ r)
              (list.map (λ(p : x86.pattern), do e <- make_environment s p.context.bindings.reverse i.operands, return (e, p)) inst.patterns)

-- def eval_simple_instruction (s : instruction) (i : decodex86.instruction) : evaluator environment :=
--   match s.patterns with
--   | [p] := do match_context p.context.bindings.reverse i.operands,
--               s <- get,
--               return s.environment
--   | _   := throw "not a simple instruction"
--   end

def instruction_family (inst : decodex86.instruction) : string :=
  let (pfx, rest) := list.span char.is_upper inst.mnemonic.to_list in
  (list.map char.to_lower pfx).as_string

def instruction_map : rbmap string instruction :=
  rbmap.from_list (list.map (λ(i : instruction), (i.mnemonic, i)) all_instructions)

def eval_instruction (s : machine_state) (i : decodex86.instruction) : except string machine_state :=
  match instruction_map.find (instruction_family i) with               
  | none := throw ("Unknown instruction: " ++ i.mnemonic)
  | (some inst) := do (sigma.mk nenv env, p) <- annotate' "pattern" (instantiate_pattern s inst i),
                      annotate' "pattern.eval" (pattern.eval nenv p env s)
                                            
/- testing -/
def get_sexp : string -> sexp := λst, 
    match sexp.from_string st with
      | (sum.inr s) := s
      | _ := sorry
    end

def string_to_instruction (s : string) : option decodex86.instruction :=
  decodex86.exec_parser decodex86.parser.instructionp (get_sexp s)

-- def go (s : string) : string := 
--   match string_to_instruction s with 
--   | none     := "No parse"
--   | (some i) := repr i.operands
--   end

-- namespace except

-- def to_sum {a} {b} : except a b -> sum a b 
--   | (except.error e) := sum.inl e
--   | (except.ok v)    := sum.inr v

-- end except

-- def go2 (s : string) (si : instruction) : string := 
--   match string_to_instruction s with 
--   | none     := "No parse"
--   | (some i) := match ((eval_simple_instruction si i).run evaluator_state.empty) with
--                 | (except.error e)   := "error: " ++ e
--                 | (except.ok (e, _)) := has_repr.repr e
--                 end
--   end

def run_get_rax (s : string) : string :=
  match string_to_instruction s with 
  | none     := "No parse"
  | (some i) := match (eval_instruction machine_state.empty i) with
                | (except.error e) := "error: " ++ e
                | (except.ok    s) := has_repr.repr (s.get_gpreg 0)
                end
 
#eval instruction_family <$> string_to_instruction "(instruction MOV32ri (register rax eax 32 0) (immediate 4 1))"

#eval run_get_rax "(instruction MOV32ri (register rax eax 32 0) (immediate 4 52))"

end x86

