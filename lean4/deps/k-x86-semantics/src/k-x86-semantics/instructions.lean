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
variable extract {n : Nat} (e : bv n) (first last : Nat) : bv (last - first)

def concat {i j:Nat} (x: bv i) (y : bv j) : bv (i + j) := prim.cat i j x y
def bv_xor {i :Nat} (x: bv i) (y : bv i) : bv i := prim.bv_xor i x y

def getRegister {t : type} (r : reg t) : semantics t := eval (expression.of_reg r)
def setRegister {t : type} (r : lhs t) (e : expression t) : semantics Unit := (set r e)

def mux {tp:type} (c:bit) (t f : tp) : tp := prim.mux tp c t f
def notBool_ (e : bit) : bit := eq e bit_zero


instance reg_lhs_coe {t : type}: HasCoe (reg t) (lhs t) := ⟨fun r => lhs.of_reg r⟩

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
      setRegister v_2598 v_5853;
      setRegister of v_5896;
      setRegister pf v_5886;
      setRegister zf v_5855;
      setRegister af v_5852;
      setRegister sf v_5847;
      setRegister cf v_5846;
      pure ()
    pat_end

end

end x86

/-
open x86

def main : io Unit := do
  monad.mapm' (io.put_str_ln ∘ repr) all_instructions
-/
