import .common
-- import system.io

namespace x86

------------------------------------------------------------------------
-- Notation

open mc_semantics
open mc_semantics.type
open reg
open semantics

notation `pattern` body `pat_end` := mk_pattern body

-- def concat {w:nat_expr} (x: bv w) (o:nat_expr) : bv o := prim.uext w o x

section
variable handleImmediateWithSignExtend (e : expression int) (n m : Nat) : expression (bv m)
variable svalueMInt {n : Nat} (e : expression (bv n)) : expression int
variable mi (n : Nat) (e : expression int) : expression (bv n)
variable extract {n : Nat} (e : expression (bv n)) (first last : Nat) : expression (bv (last - first))

def concat {i j:Nat} (x: bv i) (y : bv j) : bv (i + j) := prim.cat i j x y
def bv_xor {i :Nat} (x: bv i) (y : bv i) : bv i := prim.bv_xor i x y

def getRegister {t : type} (r : reg t) : semantics t := eval (expression.of_reg r)
def setRegister {t : type} (r : lhs t) (e : expression t) : semantics Unit := (set r e)

def mux {tp:type} (c:bit) (t f : tp) : tp := prim.mux tp c t f
def notBool_ (e : bit) : bit := eq e bit_zero


instance reg_lhs_coe {t : type}: HasCoe (reg t) (lhs t) := ⟨fun r => lhs.of_reg r⟩

@[reducible]
def R64 : Type := reg (bv 64)

@[reducible]
def Mem : Type := addr

def evaluateAddress (x : bv 64) : semantics (bv 64) := eval x

def load (ptr : expression (bv 64)) (n : Nat) : semantics (expression (bv (n * 8))) := eval (expression.read (bv (n * 8)) ptr)

def bv_nat := expression.bv_nat
def add {w:Nat} : expression (bv w) → expression (bv w) → expression (bv w) := @expression.add w

def bit_and := expression.bit_and

def addq1 : instruction :=
  definst "addq" $ do
    pattern fun (v_2596 : imm int) (v_2598 : reg (bv 64)) => do
      v_5839 <- eval (handleImmediateWithSignExtend v_2596 32 32);
      v_5840 <- eval (svalueMInt v_5839);
      v_5841 <- eval (mi 64 v_5840);
      v_5842 <- eval (concat (expression.bv_nat 1 0) v_5841);
      v_5843 <- getRegister v_2598;
      v_5844 <- eval (concat (expression.bv_nat 1 0) v_5843);
      v_5845 <- eval (expression.add v_5842 v_5844);
      v_5846 <- eval (extract v_5845 0 1);
      v_5847 <- eval (extract v_5845 1 2);
      v_5848 <- eval (extract v_5839 27 28);
      v_5849 <- eval (extract v_5843 59 60);
      v_5850 <- eval (bv_xor v_5848 v_5849);
      v_5851 <- eval (extract v_5845 60 61);
      v_5852 <- eval (bv_xor v_5850 v_5851);
      v_5853 <- eval (extract v_5845 1 65);
      v_5854 <- eval (eq v_5853 (expression.bv_nat 64 0));
      v_5855 <- eval (mux v_5854 (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      v_5856 <- eval (extract v_5845 64 65);
      v_5857 <- eval (eq v_5856 (expression.bv_nat 1 1));
      v_5858 <- eval (extract v_5845 63 64);
      v_5859 <- eval (eq v_5858 (expression.bv_nat 1 1));
      v_5860 <- eval (eq v_5857 v_5859);
      v_5861 <- eval (notBool_ v_5860);
      v_5862 <- eval (extract v_5845 62 63);
      v_5863 <- eval (eq v_5862 (expression.bv_nat 1 1));
      v_5864 <- eval (eq v_5861 v_5863);
      v_5865 <- eval (notBool_ v_5864);
      v_5866 <- eval (extract v_5845 61 62);
      v_5867 <- eval (eq v_5866 (expression.bv_nat 1 1));
      v_5868 <- eval (eq v_5865 v_5867);
      v_5869 <- eval (notBool_ v_5868);
      v_5870 <- eval (eq v_5851 (expression.bv_nat 1 1));
      v_5871 <- eval (eq v_5869 v_5870);
      v_5872 <- eval (notBool_ v_5871);
      v_5873 <- eval (extract v_5845 59 60);
      v_5874 <- eval (eq v_5873 (expression.bv_nat 1 1));
      v_5875 <- eval (eq v_5872 v_5874);
      v_5876 <- eval (notBool_ v_5875);
      v_5877 <- eval (extract v_5845 58 59);
      v_5878 <- eval (eq v_5877 (expression.bv_nat 1 1));
      v_5879 <- eval (eq v_5876 v_5878);
      v_5880 <- eval (notBool_ v_5879);
      v_5881 <- eval (extract v_5845 57 58);
      v_5882 <- eval (eq v_5881 (expression.bv_nat 1 1));
      v_5883 <- eval (eq v_5880 v_5882);
      v_5884 <- eval (notBool_ v_5883);
      v_5885 <- eval (notBool_ v_5884);
      v_5886 <- eval (mux v_5885 (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      v_5887 <- eval (extract v_5841 0 1);
      v_5888 <- eval (eq v_5887 (expression.bv_nat 1 1));
      v_5889 <- eval (extract v_5843 0 1);
      v_5890 <- eval (eq v_5889 (expression.bv_nat 1 1));
      v_5891 <- eval (eq v_5888 v_5890);
      v_5892 <- eval (eq v_5847 (expression.bv_nat 1 1));
      v_5893 <- eval (eq v_5888 v_5892);
      v_5894 <- eval (notBool_ v_5893);
      v_5895 <- eval (expression.bit_and v_5891 v_5894);
      v_5896 <- eval (mux v_5895 (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister (lhs.of_reg v_2598) v_5853;
      setRegister of v_5896;
      setRegister pf v_5886;
      setRegister zf v_5855;
      setRegister af v_5852;
      setRegister sf v_5847;
      setRegister cf v_5846;
      pure ()
    pat_end;

    pattern fun (v_2606 : Mem) (v_2607 : R64) => do
      v_11405 <- evaluateAddress v_2606;
      v_11406 <- load v_11405 8;
      v_11407 <- eval (concat (bv_nat 1 0) v_11406);
      v_11408 <- getRegister (v_2607 : R64);
      v_11409 <- eval (concat (bv_nat 1 0) v_11408);
      v_11410 <- eval (add v_11407 v_11409);
      v_11411 <- eval (extract v_11410 0 1);
      v_11412 <- eval (extract v_11410 1 2);
      v_11413 <- eval (extract v_11410 1 65); 
      v_11414 <- eval (eq v_11413 (bv_nat 64 0));
      v_11415 <- eval (mux v_11414 (bv_nat 1 1) (bv_nat 1 0));
      v_11416 <- eval (extract v_11406 59 60);
      v_11417 <- eval (extract v_11408 59 60);
      v_11418 <- eval (bv_xor v_11416 v_11417);
      v_11419 <- eval (extract v_11410 60 61);
      v_11420 <- eval (bv_xor v_11418 v_11419);
      v_11421 <- eval (extract v_11410 64 65);
      v_11422 <- eval (eq v_11421 (bv_nat 1 1));
      v_11423 <- eval (extract v_11410 63 64);
      v_11424 <- eval (eq v_11423 (bv_nat 1 1));
      v_11425 <- eval (eq v_11422 v_11424);
      v_11426 <- eval (notBool_ v_11425);
      v_11427 <- eval (extract v_11410 62 63);
      v_11428 <- eval (eq v_11427 (bv_nat 1 1));
      v_11429 <- eval (eq v_11426 v_11428);
      v_11430 <- eval (notBool_ v_11429);
      v_11431 <- eval (extract v_11410 61 62);
      v_11432 <- eval (eq v_11431 (bv_nat 1 1));
      v_11433 <- eval (eq v_11430 v_11432);
      v_11434 <- eval (notBool_ v_11433);
      v_11435 <- eval (eq v_11419 (bv_nat 1 1));
      v_11436 <- eval (eq v_11434 v_11435);
      v_11437 <- eval (notBool_ v_11436);
      v_11438 <- eval (extract v_11410 59 60);
      v_11439 <- eval (eq v_11438 (bv_nat 1 1));
      v_11440 <- eval (eq v_11437 v_11439);
      v_11441 <- eval (notBool_ v_11440);
      v_11442 <- eval (extract v_11410 58 59);
      v_11443 <- eval (eq v_11442 (bv_nat 1 1));
      v_11444 <- eval (eq v_11441 v_11443);
      v_11445 <- eval (notBool_ v_11444);
      v_11446 <- eval (extract v_11410 57 58);
      v_11447 <- eval (eq v_11446 (bv_nat 1 1));
      v_11448 <- eval (eq v_11445 v_11447);
      v_11449 <- eval (notBool_ v_11448);
      v_11450 <- eval (notBool_ v_11449);
      v_11451 <- eval (mux v_11450 (bv_nat 1 1) (bv_nat 1 0));
      v_11452 <- eval (extract v_11406 0 1);
      v_11453 <- eval (eq v_11452 (bv_nat 1 1));
      v_11454 <- eval (extract v_11408 0 1);
      v_11455 <- eval (eq v_11454 (bv_nat 1 1));
      v_11456 <- eval (eq v_11453 v_11455);
      v_11457 <- eval (eq v_11412 (bv_nat 1 1));
      v_11458 <- eval (eq v_11453 v_11457);
      v_11459 <- eval (notBool_ v_11458);
      v_11460 <- eval (bit_and v_11456 v_11459);
      v_11461 <- eval (mux v_11460 (bv_nat 1 1) (bv_nat 1 0));
      setRegister (lhs.of_reg v_2607) v_11413;
      setRegister of v_11461;
      setRegister pf v_11451;
      setRegister af v_11420;
      setRegister zf v_11415;
      setRegister sf v_11412;
      setRegister cf v_11411;
      pure ()
    pat_end

end

end x86

/-
open x86

def main : io Unit := do
  monad.mapm' (io.put_str_ln ∘ repr) all_instructions
-/
