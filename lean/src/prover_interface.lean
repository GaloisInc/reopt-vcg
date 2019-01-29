universes u v

--open smt2

-- A word 64
def word64 := { x : ℕ // x < 2^64 }

@[reducible]
def llvm_instruction_index := ℕ

@[reducible]
def mc_instruction_addr := word64

-- The main interface to the verification condition generator.
class is_vcg (m : Type u → Type v) :=
(start_llvm_instruction : llvm_instruction_index → m punit)
(start_mc_instruction   : mc_instruction_addr → m punit)
--(check_sat_assuming : string → list (term bool) → m punit)
(fail : string → m punit)

-- Use cases:
-- 1. Generate SMTLIB files for each proof.
-- 2. Call SMT solver
-- 3. Write assertion about what we proved.
