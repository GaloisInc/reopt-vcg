def shll1 : instruction :=
  definst "shll" $ do
    pattern fun cl (v_2769 : reg (bv 32)) => do
      v_4757 <- getRegister rcx;
      v_4759 <- eval (bv_and (extract v_4757 56 64) (expression.bv_nat 8 31));
      v_4760 <- eval (uge v_4759 (expression.bv_nat 8 32));
      v_4763 <- eval (eq v_4759 (expression.bv_nat 8 0));
      v_4764 <- eval (notBool_ v_4763);
      v_4765 <- getRegister v_2769;
      v_4770 <- eval (extract (shl (concat (expression.bv_nat 1 0) v_4765) (uvalueMInt (concat (expression.bv_nat 25 0) v_4759))) 0 33);
      v_4774 <- getRegister cf;
      v_4779 <- eval (bit_or (bit_and v_4760 undef) (bit_and (notBool_ v_4760) (bit_or (bit_and v_4764 (eq (extract v_4770 0 1) (expression.bv_nat 1 1))) (bit_and v_4763 (eq v_4774 (expression.bv_nat 1 1))))));
      v_4782 <- eval (eq (extract v_4770 1 2) (expression.bv_nat 1 1));
      v_4784 <- getRegister sf;
      v_4789 <- eval (bit_and v_4764 undef);
      v_4790 <- getRegister af;
      v_4795 <- eval (extract v_4770 1 33);
      v_4798 <- getRegister zf;
      v_4833 <- getRegister pf;
      v_4838 <- eval (eq v_4759 (expression.bv_nat 8 1));
      v_4843 <- getRegister of;
      setRegister (lhs.of_reg v_2769) v_4795;
      setRegister of (mux (bit_or (bit_and v_4838 (notBool_ (eq v_4779 v_4782))) (bit_and (notBool_ v_4838) (bit_or v_4789 (bit_and v_4763 (eq v_4843 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (mux (bit_or (bit_and v_4764 (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (eq (extract v_4770 32 33) (expression.bv_nat 1 1)) (eq (extract v_4770 31 32) (expression.bv_nat 1 1)))) (eq (extract v_4770 30 31) (expression.bv_nat 1 1)))) (eq (extract v_4770 29 30) (expression.bv_nat 1 1)))) (eq (extract v_4770 28 29) (expression.bv_nat 1 1)))) (eq (extract v_4770 27 28) (expression.bv_nat 1 1)))) (eq (extract v_4770 26 27) (expression.bv_nat 1 1)))) (eq (extract v_4770 25 26) (expression.bv_nat 1 1)))) (bit_and v_4763 (eq v_4833 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (mux (bit_or (bit_and v_4764 (eq v_4795 (expression.bv_nat 32 0))) (bit_and v_4763 (eq v_4798 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister af (mux (bit_or v_4789 (bit_and v_4763 (eq v_4790 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister sf (mux (bit_or (bit_and v_4764 v_4782) (bit_and v_4763 (eq v_4784 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux v_4779 (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_2772 : imm int) (v_2774 : reg (bv 32)) => do
      v_4858 <- eval (bv_and (handleImmediateWithSignExtend v_2772 8 8) (expression.bv_nat 8 31));
      v_4859 <- eval (uge v_4858 (expression.bv_nat 8 32));
      v_4862 <- eval (eq v_4858 (expression.bv_nat 8 0));
      v_4863 <- eval (notBool_ v_4862);
      v_4864 <- getRegister v_2774;
      v_4869 <- eval (extract (shl (concat (expression.bv_nat 1 0) v_4864) (uvalueMInt (concat (expression.bv_nat 25 0) v_4858))) 0 33);
      v_4873 <- getRegister cf;
      v_4878 <- eval (bit_or (bit_and v_4859 undef) (bit_and (notBool_ v_4859) (bit_or (bit_and v_4863 (eq (extract v_4869 0 1) (expression.bv_nat 1 1))) (bit_and v_4862 (eq v_4873 (expression.bv_nat 1 1))))));
      v_4881 <- eval (eq (extract v_4869 1 2) (expression.bv_nat 1 1));
      v_4883 <- getRegister sf;
      v_4888 <- eval (bit_and v_4863 undef);
      v_4889 <- getRegister af;
      v_4894 <- eval (extract v_4869 1 33);
      v_4897 <- getRegister zf;
      v_4932 <- getRegister pf;
      v_4937 <- eval (eq v_4858 (expression.bv_nat 8 1));
      v_4942 <- getRegister of;
      setRegister (lhs.of_reg v_2774) v_4894;
      setRegister of (mux (bit_or (bit_and v_4937 (notBool_ (eq v_4878 v_4881))) (bit_and (notBool_ v_4937) (bit_or v_4888 (bit_and v_4862 (eq v_4942 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (mux (bit_or (bit_and v_4863 (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (eq (extract v_4869 32 33) (expression.bv_nat 1 1)) (eq (extract v_4869 31 32) (expression.bv_nat 1 1)))) (eq (extract v_4869 30 31) (expression.bv_nat 1 1)))) (eq (extract v_4869 29 30) (expression.bv_nat 1 1)))) (eq (extract v_4869 28 29) (expression.bv_nat 1 1)))) (eq (extract v_4869 27 28) (expression.bv_nat 1 1)))) (eq (extract v_4869 26 27) (expression.bv_nat 1 1)))) (eq (extract v_4869 25 26) (expression.bv_nat 1 1)))) (bit_and v_4862 (eq v_4932 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (mux (bit_or (bit_and v_4863 (eq v_4894 (expression.bv_nat 32 0))) (bit_and v_4862 (eq v_4897 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister af (mux (bit_or v_4888 (bit_and v_4862 (eq v_4889 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister sf (mux (bit_or (bit_and v_4863 v_4881) (bit_and v_4862 (eq v_4883 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux v_4878 (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun $0x1 (v_2778 : reg (bv 32)) => do
      v_4956 <- getRegister v_2778;
      v_4959 <- eval (extract (shl (concat (expression.bv_nat 1 0) v_4956) 1) 0 33);
      v_4960 <- eval (extract v_4959 0 1);
      v_4961 <- eval (extract v_4959 1 2);
      v_4962 <- eval (extract v_4959 1 33);
      setRegister (lhs.of_reg v_2778) v_4962;
      setRegister of (mux (notBool_ (eq (eq v_4960 (expression.bv_nat 1 1)) (eq v_4961 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_4959 25 33));
      setRegister zf (zeroFlag v_4962);
      setRegister af undef;
      setRegister sf v_4961;
      setRegister cf v_4960;
      pure ()
    pat_end;
    pattern fun cl (v_2758 : Mem) => do
      v_10964 <- evaluateAddress v_2758;
      v_10965 <- load v_10964 4;
      v_10967 <- getRegister rcx;
      v_10969 <- eval (bv_and (extract v_10967 56 64) (expression.bv_nat 8 31));
      v_10973 <- eval (extract (shl (concat (expression.bv_nat 1 0) v_10965) (uvalueMInt (concat (expression.bv_nat 25 0) v_10969))) 0 33);
      v_10974 <- eval (extract v_10973 1 33);
      store v_10964 v_10974 4;
      v_10976 <- eval (uge v_10969 (expression.bv_nat 8 32));
      v_10979 <- eval (eq v_10969 (expression.bv_nat 8 0));
      v_10980 <- eval (notBool_ v_10979);
      v_10984 <- getRegister cf;
      v_10989 <- eval (bit_or (bit_and v_10976 undef) (bit_and (notBool_ v_10976) (bit_or (bit_and v_10980 (eq (extract v_10973 0 1) (expression.bv_nat 1 1))) (bit_and v_10979 (eq v_10984 (expression.bv_nat 1 1))))));
      v_10992 <- eval (eq (extract v_10973 1 2) (expression.bv_nat 1 1));
      v_10994 <- getRegister sf;
      v_11001 <- getRegister zf;
      v_11006 <- eval (bit_and v_10980 undef);
      v_11007 <- getRegister af;
      v_11042 <- getRegister pf;
      v_11047 <- eval (eq v_10969 (expression.bv_nat 8 1));
      v_11052 <- getRegister of;
      setRegister of (mux (bit_or (bit_and v_11047 (notBool_ (eq v_10989 v_10992))) (bit_and (notBool_ v_11047) (bit_or v_11006 (bit_and v_10979 (eq v_11052 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (mux (bit_or (bit_and v_10980 (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (eq (extract v_10973 32 33) (expression.bv_nat 1 1)) (eq (extract v_10973 31 32) (expression.bv_nat 1 1)))) (eq (extract v_10973 30 31) (expression.bv_nat 1 1)))) (eq (extract v_10973 29 30) (expression.bv_nat 1 1)))) (eq (extract v_10973 28 29) (expression.bv_nat 1 1)))) (eq (extract v_10973 27 28) (expression.bv_nat 1 1)))) (eq (extract v_10973 26 27) (expression.bv_nat 1 1)))) (eq (extract v_10973 25 26) (expression.bv_nat 1 1)))) (bit_and v_10979 (eq v_11042 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister af (mux (bit_or v_11006 (bit_and v_10979 (eq v_11007 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (mux (bit_or (bit_and v_10980 (eq v_10974 (expression.bv_nat 32 0))) (bit_and v_10979 (eq v_11001 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister sf (mux (bit_or (bit_and v_10980 v_10992) (bit_and v_10979 (eq v_10994 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux v_10989 (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_2761 : imm int) (v_2762 : Mem) => do
      v_11065 <- evaluateAddress v_2762;
      v_11066 <- load v_11065 4;
      v_11069 <- eval (bv_and (handleImmediateWithSignExtend v_2761 8 8) (expression.bv_nat 8 31));
      v_11073 <- eval (extract (shl (concat (expression.bv_nat 1 0) v_11066) (uvalueMInt (concat (expression.bv_nat 25 0) v_11069))) 0 33);
      v_11074 <- eval (extract v_11073 1 33);
      store v_11065 v_11074 4;
      v_11076 <- eval (uge v_11069 (expression.bv_nat 8 32));
      v_11079 <- eval (eq v_11069 (expression.bv_nat 8 0));
      v_11080 <- eval (notBool_ v_11079);
      v_11084 <- getRegister cf;
      v_11089 <- eval (bit_or (bit_and v_11076 undef) (bit_and (notBool_ v_11076) (bit_or (bit_and v_11080 (eq (extract v_11073 0 1) (expression.bv_nat 1 1))) (bit_and v_11079 (eq v_11084 (expression.bv_nat 1 1))))));
      v_11092 <- eval (eq (extract v_11073 1 2) (expression.bv_nat 1 1));
      v_11094 <- getRegister sf;
      v_11101 <- getRegister zf;
      v_11106 <- eval (bit_and v_11080 undef);
      v_11107 <- getRegister af;
      v_11142 <- getRegister pf;
      v_11147 <- eval (eq v_11069 (expression.bv_nat 8 1));
      v_11152 <- getRegister of;
      setRegister of (mux (bit_or (bit_and v_11147 (notBool_ (eq v_11089 v_11092))) (bit_and (notBool_ v_11147) (bit_or v_11106 (bit_and v_11079 (eq v_11152 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (mux (bit_or (bit_and v_11080 (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (eq (extract v_11073 32 33) (expression.bv_nat 1 1)) (eq (extract v_11073 31 32) (expression.bv_nat 1 1)))) (eq (extract v_11073 30 31) (expression.bv_nat 1 1)))) (eq (extract v_11073 29 30) (expression.bv_nat 1 1)))) (eq (extract v_11073 28 29) (expression.bv_nat 1 1)))) (eq (extract v_11073 27 28) (expression.bv_nat 1 1)))) (eq (extract v_11073 26 27) (expression.bv_nat 1 1)))) (eq (extract v_11073 25 26) (expression.bv_nat 1 1)))) (bit_and v_11079 (eq v_11142 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister af (mux (bit_or v_11106 (bit_and v_11079 (eq v_11107 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (mux (bit_or (bit_and v_11080 (eq v_11074 (expression.bv_nat 32 0))) (bit_and v_11079 (eq v_11101 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister sf (mux (bit_or (bit_and v_11080 v_11092) (bit_and v_11079 (eq v_11094 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux v_11089 (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end
