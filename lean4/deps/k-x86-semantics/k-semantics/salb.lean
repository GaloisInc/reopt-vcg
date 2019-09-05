def salb1 : instruction :=
  definst "salb" $ do
    pattern fun cl (v_2960 : reg (bv 8)) => do
      v_5755 <- getRegister rcx;
      v_5757 <- eval (bv_and (extract v_5755 56 64) (expression.bv_nat 8 31));
      v_5758 <- eval (eq v_5757 (expression.bv_nat 8 0));
      v_5759 <- eval (notBool_ v_5758);
      v_5760 <- getRegister v_2960;
      v_5764 <- eval (extract (shl (concat (expression.bv_nat 1 0) v_5760) (concat (expression.bv_nat 1 0) v_5757)) 0 9);
      v_5765 <- eval (extract v_5764 1 9);
      v_5768 <- getRegister zf;
      v_5772 <- eval (isBitSet v_5764 1);
      v_5774 <- getRegister sf;
      v_5780 <- getRegister pf;
      v_5784 <- eval (eq v_5757 (expression.bv_nat 8 1));
      v_5785 <- eval (uge v_5757 (expression.bv_nat 8 8));
      v_5790 <- getRegister cf;
      v_5795 <- eval (bit_or (bit_and v_5785 undef) (bit_and (notBool_ v_5785) (bit_or (bit_and v_5759 (isBitSet v_5764 0)) (bit_and v_5758 (eq v_5790 (expression.bv_nat 1 1))))));
      v_5800 <- eval (bit_and v_5759 undef);
      v_5801 <- getRegister of;
      v_5807 <- getRegister af;
      setRegister (lhs.of_reg v_2960) v_5765;
      setRegister af (bit_or v_5800 (bit_and v_5758 (eq v_5807 (expression.bv_nat 1 1))));
      setRegister cf v_5795;
      setRegister of (bit_or (bit_and v_5784 (notBool_ (eq v_5795 v_5772))) (bit_and (notBool_ v_5784) (bit_or v_5800 (bit_and v_5758 (eq v_5801 (expression.bv_nat 1 1))))));
      setRegister pf (bit_or (bit_and v_5759 (parityFlag v_5765)) (bit_and v_5758 (eq v_5780 (expression.bv_nat 1 1))));
      setRegister sf (bit_or (bit_and v_5759 v_5772) (bit_and v_5758 (eq v_5774 (expression.bv_nat 1 1))));
      setRegister zf (bit_or (bit_and v_5759 (eq v_5765 (expression.bv_nat 8 0))) (bit_and v_5758 (eq v_5768 (expression.bv_nat 1 1))));
      pure ()
    pat_end;
    pattern fun (v_2963 : imm int) (v_2965 : reg (bv 8)) => do
      v_5819 <- eval (bv_and (handleImmediateWithSignExtend v_2963 8 8) (expression.bv_nat 8 31));
      v_5820 <- eval (eq v_5819 (expression.bv_nat 8 0));
      v_5821 <- eval (notBool_ v_5820);
      v_5822 <- getRegister v_2965;
      v_5826 <- eval (extract (shl (concat (expression.bv_nat 1 0) v_5822) (concat (expression.bv_nat 1 0) v_5819)) 0 9);
      v_5827 <- eval (extract v_5826 1 9);
      v_5830 <- getRegister zf;
      v_5834 <- eval (isBitSet v_5826 1);
      v_5836 <- getRegister sf;
      v_5842 <- getRegister pf;
      v_5846 <- eval (eq v_5819 (expression.bv_nat 8 1));
      v_5847 <- eval (uge v_5819 (expression.bv_nat 8 8));
      v_5852 <- getRegister cf;
      v_5857 <- eval (bit_or (bit_and v_5847 undef) (bit_and (notBool_ v_5847) (bit_or (bit_and v_5821 (isBitSet v_5826 0)) (bit_and v_5820 (eq v_5852 (expression.bv_nat 1 1))))));
      v_5862 <- eval (bit_and v_5821 undef);
      v_5863 <- getRegister of;
      v_5869 <- getRegister af;
      setRegister (lhs.of_reg v_2965) v_5827;
      setRegister af (bit_or v_5862 (bit_and v_5820 (eq v_5869 (expression.bv_nat 1 1))));
      setRegister cf v_5857;
      setRegister of (bit_or (bit_and v_5846 (notBool_ (eq v_5857 v_5834))) (bit_and (notBool_ v_5846) (bit_or v_5862 (bit_and v_5820 (eq v_5863 (expression.bv_nat 1 1))))));
      setRegister pf (bit_or (bit_and v_5821 (parityFlag v_5827)) (bit_and v_5820 (eq v_5842 (expression.bv_nat 1 1))));
      setRegister sf (bit_or (bit_and v_5821 v_5834) (bit_and v_5820 (eq v_5836 (expression.bv_nat 1 1))));
      setRegister zf (bit_or (bit_and v_5821 (eq v_5827 (expression.bv_nat 8 0))) (bit_and v_5820 (eq v_5830 (expression.bv_nat 1 1))));
      pure ()
    pat_end;
    pattern fun (v_2968 : reg (bv 8)) => do
      v_8218 <- getRegister v_2968;
      v_8221 <- eval (extract (shl (concat (expression.bv_nat 1 0) v_8218) (expression.bv_nat 9 1)) 0 9);
      v_8222 <- eval (extract v_8221 1 9);
      v_8224 <- eval (isBitSet v_8221 1);
      v_8226 <- eval (isBitSet v_8221 0);
      setRegister (lhs.of_reg v_2968) v_8222;
      setRegister af undef;
      setRegister cf v_8226;
      setRegister of (notBool_ (eq v_8226 v_8224));
      setRegister pf (parityFlag v_8222);
      setRegister sf v_8224;
      setRegister zf (zeroFlag v_8222);
      pure ()
    pat_end;
    pattern fun cl (v_2930 : Mem) => do
      v_12879 <- evaluateAddress v_2930;
      v_12880 <- load v_12879 1;
      v_12882 <- getRegister rcx;
      v_12884 <- eval (bv_and (extract v_12882 56 64) (expression.bv_nat 8 31));
      v_12887 <- eval (extract (shl (concat (expression.bv_nat 1 0) v_12880) (concat (expression.bv_nat 1 0) v_12884)) 0 9);
      v_12888 <- eval (extract v_12887 1 9);
      store v_12879 v_12888 1;
      v_12890 <- eval (eq v_12884 (expression.bv_nat 8 0));
      v_12891 <- eval (notBool_ v_12890);
      v_12894 <- getRegister zf;
      v_12898 <- eval (isBitSet v_12887 1);
      v_12900 <- getRegister sf;
      v_12906 <- getRegister pf;
      v_12910 <- eval (eq v_12884 (expression.bv_nat 8 1));
      v_12911 <- eval (uge v_12884 (expression.bv_nat 8 8));
      v_12916 <- getRegister cf;
      v_12921 <- eval (bit_or (bit_and v_12911 undef) (bit_and (notBool_ v_12911) (bit_or (bit_and v_12891 (isBitSet v_12887 0)) (bit_and v_12890 (eq v_12916 (expression.bv_nat 1 1))))));
      v_12926 <- eval (bit_and v_12891 undef);
      v_12927 <- getRegister of;
      v_12933 <- getRegister af;
      setRegister af (bit_or v_12926 (bit_and v_12890 (eq v_12933 (expression.bv_nat 1 1))));
      setRegister cf v_12921;
      setRegister of (bit_or (bit_and v_12910 (notBool_ (eq v_12921 v_12898))) (bit_and (notBool_ v_12910) (bit_or v_12926 (bit_and v_12890 (eq v_12927 (expression.bv_nat 1 1))))));
      setRegister pf (bit_or (bit_and v_12891 (parityFlag v_12888)) (bit_and v_12890 (eq v_12906 (expression.bv_nat 1 1))));
      setRegister sf (bit_or (bit_and v_12891 v_12898) (bit_and v_12890 (eq v_12900 (expression.bv_nat 1 1))));
      setRegister zf (bit_or (bit_and v_12891 (eq v_12888 (expression.bv_nat 8 0))) (bit_and v_12890 (eq v_12894 (expression.bv_nat 1 1))));
      pure ()
    pat_end;
    pattern fun (v_2933 : imm int) (v_2934 : Mem) => do
      v_12943 <- evaluateAddress v_2934;
      v_12944 <- load v_12943 1;
      v_12947 <- eval (bv_and (handleImmediateWithSignExtend v_2933 8 8) (expression.bv_nat 8 31));
      v_12950 <- eval (extract (shl (concat (expression.bv_nat 1 0) v_12944) (concat (expression.bv_nat 1 0) v_12947)) 0 9);
      v_12951 <- eval (extract v_12950 1 9);
      store v_12943 v_12951 1;
      v_12953 <- eval (eq v_12947 (expression.bv_nat 8 0));
      v_12954 <- eval (notBool_ v_12953);
      v_12957 <- getRegister zf;
      v_12961 <- eval (isBitSet v_12950 1);
      v_12963 <- getRegister sf;
      v_12969 <- getRegister pf;
      v_12973 <- eval (eq v_12947 (expression.bv_nat 8 1));
      v_12974 <- eval (uge v_12947 (expression.bv_nat 8 8));
      v_12979 <- getRegister cf;
      v_12984 <- eval (bit_or (bit_and v_12974 undef) (bit_and (notBool_ v_12974) (bit_or (bit_and v_12954 (isBitSet v_12950 0)) (bit_and v_12953 (eq v_12979 (expression.bv_nat 1 1))))));
      v_12989 <- eval (bit_and v_12954 undef);
      v_12990 <- getRegister of;
      v_12996 <- getRegister af;
      setRegister af (bit_or v_12989 (bit_and v_12953 (eq v_12996 (expression.bv_nat 1 1))));
      setRegister cf v_12984;
      setRegister of (bit_or (bit_and v_12973 (notBool_ (eq v_12984 v_12961))) (bit_and (notBool_ v_12973) (bit_or v_12989 (bit_and v_12953 (eq v_12990 (expression.bv_nat 1 1))))));
      setRegister pf (bit_or (bit_and v_12954 (parityFlag v_12951)) (bit_and v_12953 (eq v_12969 (expression.bv_nat 1 1))));
      setRegister sf (bit_or (bit_and v_12954 v_12961) (bit_and v_12953 (eq v_12963 (expression.bv_nat 1 1))));
      setRegister zf (bit_or (bit_and v_12954 (eq v_12951 (expression.bv_nat 8 0))) (bit_and v_12953 (eq v_12957 (expression.bv_nat 1 1))));
      pure ()
    pat_end;
    pattern fun (v_2937 : Mem) => do
      v_14491 <- evaluateAddress v_2937;
      v_14492 <- load v_14491 1;
      v_14495 <- eval (extract (shl (concat (expression.bv_nat 1 0) v_14492) (expression.bv_nat 9 1)) 0 9);
      v_14496 <- eval (extract v_14495 1 9);
      store v_14491 v_14496 1;
      v_14499 <- eval (isBitSet v_14495 1);
      v_14501 <- eval (isBitSet v_14495 0);
      setRegister af undef;
      setRegister cf v_14501;
      setRegister of (notBool_ (eq v_14501 v_14499));
      setRegister pf (parityFlag v_14496);
      setRegister sf v_14499;
      setRegister zf (zeroFlag v_14496);
      pure ()
    pat_end
