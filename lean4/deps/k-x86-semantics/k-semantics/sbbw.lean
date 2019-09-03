def sbbw1 : instruction :=
  definst "sbbw" $ do
    pattern fun (v_3278 : imm int) ax => do
      v_8807 <- getRegister cf;
      v_8809 <- eval (handleImmediateWithSignExtend v_3278 16 16);
      v_8813 <- eval (concat (expression.bv_nat 1 0) (bv_xor v_8809 (mi (bitwidthMInt v_8809) -1)));
      v_8816 <- getRegister rax;
      v_8819 <- eval (add (mux (eq v_8807 (expression.bv_nat 1 1)) v_8813 (add v_8813 (expression.bv_nat 17 1))) (concat (expression.bv_nat 1 0) (extract v_8816 48 64)));
      v_8824 <- eval (extract v_8819 1 2);
      v_8830 <- eval (extract v_8819 1 17);
      v_8834 <- eval (extract v_8809 0 1);
      v_8838 <- eval (eq (bv_xor v_8834 (mi (bitwidthMInt v_8834) -1)) (expression.bv_nat 1 1));
      setRegister rax (concat (extract v_8816 0 48) v_8830);
      setRegister of (mux (bit_and (eq v_8838 (eq (extract v_8816 48 49) (expression.bv_nat 1 1))) (notBool_ (eq v_8838 (eq v_8824 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_8819 9 17));
      setRegister zf (zeroFlag v_8830);
      setRegister af (bv_xor (bv_xor (extract v_8809 11 12) (extract v_8816 59 60)) (extract v_8819 12 13));
      setRegister sf v_8824;
      setRegister cf (mux (notBool_ (eq (extract v_8819 0 1) (expression.bv_nat 1 1))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_3290 : imm int) (v_3292 : reg (bv 16)) => do
      v_8864 <- getRegister cf;
      v_8866 <- eval (handleImmediateWithSignExtend v_3290 16 16);
      v_8870 <- eval (concat (expression.bv_nat 1 0) (bv_xor v_8866 (mi (bitwidthMInt v_8866) -1)));
      v_8873 <- getRegister v_3292;
      v_8875 <- eval (add (mux (eq v_8864 (expression.bv_nat 1 1)) v_8870 (add v_8870 (expression.bv_nat 17 1))) (concat (expression.bv_nat 1 0) v_8873));
      v_8880 <- eval (extract v_8875 1 2);
      v_8885 <- eval (extract v_8875 1 17);
      v_8889 <- eval (extract v_8866 0 1);
      v_8893 <- eval (eq (bv_xor v_8889 (mi (bitwidthMInt v_8889) -1)) (expression.bv_nat 1 1));
      setRegister (lhs.of_reg v_3292) v_8885;
      setRegister of (mux (bit_and (eq v_8893 (eq (extract v_8873 0 1) (expression.bv_nat 1 1))) (notBool_ (eq v_8893 (eq v_8880 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_8875 9 17));
      setRegister zf (zeroFlag v_8885);
      setRegister af (bv_xor (extract (bv_xor v_8866 v_8873) 11 12) (extract v_8875 12 13));
      setRegister sf v_8880;
      setRegister cf (mux (notBool_ (eq (extract v_8875 0 1) (expression.bv_nat 1 1))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_3300 : reg (bv 16)) (v_3301 : reg (bv 16)) => do
      v_8913 <- getRegister cf;
      v_8915 <- getRegister v_3300;
      v_8919 <- eval (concat (expression.bv_nat 1 0) (bv_xor v_8915 (mi (bitwidthMInt v_8915) -1)));
      v_8922 <- getRegister v_3301;
      v_8924 <- eval (add (mux (eq v_8913 (expression.bv_nat 1 1)) v_8919 (add v_8919 (expression.bv_nat 17 1))) (concat (expression.bv_nat 1 0) v_8922));
      v_8929 <- eval (extract v_8924 1 2);
      v_8934 <- eval (extract v_8924 1 17);
      v_8938 <- eval (extract v_8915 0 1);
      v_8942 <- eval (eq (bv_xor v_8938 (mi (bitwidthMInt v_8938) -1)) (expression.bv_nat 1 1));
      setRegister (lhs.of_reg v_3301) v_8934;
      setRegister of (mux (bit_and (eq v_8942 (eq (extract v_8922 0 1) (expression.bv_nat 1 1))) (notBool_ (eq v_8942 (eq v_8929 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_8924 9 17));
      setRegister zf (zeroFlag v_8934);
      setRegister af (bv_xor (extract (bv_xor v_8915 v_8922) 11 12) (extract v_8924 12 13));
      setRegister sf v_8929;
      setRegister cf (mux (notBool_ (eq (extract v_8924 0 1) (expression.bv_nat 1 1))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_3293 : Mem) (v_3296 : reg (bv 16)) => do
      v_13385 <- getRegister cf;
      v_13387 <- evaluateAddress v_3293;
      v_13388 <- load v_13387 2;
      v_13392 <- eval (concat (expression.bv_nat 1 0) (bv_xor v_13388 (mi (bitwidthMInt v_13388) -1)));
      v_13395 <- getRegister v_3296;
      v_13397 <- eval (add (mux (eq v_13385 (expression.bv_nat 1 1)) v_13392 (add v_13392 (expression.bv_nat 17 1))) (concat (expression.bv_nat 1 0) v_13395));
      v_13402 <- eval (extract v_13397 1 2);
      v_13407 <- eval (extract v_13397 1 17);
      v_13411 <- eval (extract v_13388 0 1);
      v_13415 <- eval (eq (bv_xor v_13411 (mi (bitwidthMInt v_13411) -1)) (expression.bv_nat 1 1));
      setRegister (lhs.of_reg v_3296) v_13407;
      setRegister of (mux (bit_and (eq v_13415 (eq (extract v_13395 0 1) (expression.bv_nat 1 1))) (notBool_ (eq v_13415 (eq v_13402 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_13397 9 17));
      setRegister zf (zeroFlag v_13407);
      setRegister af (bv_xor (extract (bv_xor v_13388 v_13395) 11 12) (extract v_13397 12 13));
      setRegister sf v_13402;
      setRegister cf (mux (notBool_ (eq (extract v_13397 0 1) (expression.bv_nat 1 1))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_3283 : imm int) (v_3280 : Mem) => do
      v_18065 <- evaluateAddress v_3280;
      v_18066 <- getRegister cf;
      v_18068 <- eval (handleImmediateWithSignExtend v_3283 16 16);
      v_18072 <- eval (concat (expression.bv_nat 1 0) (bv_xor v_18068 (mi (bitwidthMInt v_18068) -1)));
      v_18075 <- load v_18065 2;
      v_18077 <- eval (add (mux (eq v_18066 (expression.bv_nat 1 1)) v_18072 (add v_18072 (expression.bv_nat 17 1))) (concat (expression.bv_nat 1 0) v_18075));
      v_18078 <- eval (extract v_18077 1 17);
      store v_18065 v_18078 2;
      v_18084 <- eval (extract v_18077 1 2);
      v_18092 <- eval (extract v_18068 0 1);
      v_18096 <- eval (eq (bv_xor v_18092 (mi (bitwidthMInt v_18092) -1)) (expression.bv_nat 1 1));
      setRegister of (mux (bit_and (eq v_18096 (eq (extract v_18075 0 1) (expression.bv_nat 1 1))) (notBool_ (eq v_18096 (eq v_18084 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_18077 9 17));
      setRegister af (bv_xor (extract (bv_xor v_18068 v_18075) 11 12) (extract v_18077 12 13));
      setRegister zf (zeroFlag v_18078);
      setRegister sf v_18084;
      setRegister cf (mux (notBool_ (eq (extract v_18077 0 1) (expression.bv_nat 1 1))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_3287 : reg (bv 16)) (v_3284 : Mem) => do
      v_18111 <- evaluateAddress v_3284;
      v_18112 <- getRegister cf;
      v_18114 <- getRegister v_3287;
      v_18118 <- eval (concat (expression.bv_nat 1 0) (bv_xor v_18114 (mi (bitwidthMInt v_18114) -1)));
      v_18121 <- load v_18111 2;
      v_18123 <- eval (add (mux (eq v_18112 (expression.bv_nat 1 1)) v_18118 (add v_18118 (expression.bv_nat 17 1))) (concat (expression.bv_nat 1 0) v_18121));
      v_18124 <- eval (extract v_18123 1 17);
      store v_18111 v_18124 2;
      v_18130 <- eval (extract v_18123 1 2);
      v_18138 <- eval (extract v_18114 0 1);
      v_18142 <- eval (eq (bv_xor v_18138 (mi (bitwidthMInt v_18138) -1)) (expression.bv_nat 1 1));
      setRegister of (mux (bit_and (eq v_18142 (eq (extract v_18121 0 1) (expression.bv_nat 1 1))) (notBool_ (eq v_18142 (eq v_18130 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_18123 9 17));
      setRegister af (bv_xor (extract (bv_xor v_18114 v_18121) 11 12) (extract v_18123 12 13));
      setRegister zf (zeroFlag v_18124);
      setRegister sf v_18130;
      setRegister cf (mux (notBool_ (eq (extract v_18123 0 1) (expression.bv_nat 1 1))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end
