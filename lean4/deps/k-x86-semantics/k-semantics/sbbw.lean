def sbbw1 : instruction :=
  definst "sbbw" $ do
    pattern fun (v_3381 : imm int) (v_3382 : reg (bv 16)) => do
      v_6952 <- getRegister cf;
      v_6953 <- eval (handleImmediateWithSignExtend v_3381 16 16);
      v_6955 <- eval (concat (expression.bv_nat 1 0) (bv_xor v_6953 (expression.bv_nat 16 65535)));
      v_6958 <- getRegister v_3382;
      v_6960 <- eval (add (mux v_6952 v_6955 (add v_6955 (expression.bv_nat 17 1))) (concat (expression.bv_nat 1 0) v_6958));
      v_6961 <- eval (extract v_6960 1 17);
      v_6963 <- eval (isBitSet v_6960 1);
      v_6968 <- eval (eq (bv_xor (extract v_6953 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1));
      setRegister (lhs.of_reg v_3382) v_6961;
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_6953 v_6958) 11) (isBitSet v_6960 12)));
      setRegister cf (isBitClear v_6960 0);
      setRegister of (bit_and (eq v_6968 (isBitSet v_6958 0)) (notBool_ (eq v_6968 v_6963)));
      setRegister pf (parityFlag (extract v_6960 9 17));
      setRegister sf v_6963;
      setRegister zf (zeroFlag v_6961);
      pure ()
    pat_end;
    pattern fun (v_3390 : reg (bv 16)) (v_3391 : reg (bv 16)) => do
      v_6991 <- getRegister cf;
      v_6992 <- getRegister v_3390;
      v_6994 <- eval (concat (expression.bv_nat 1 0) (bv_xor v_6992 (expression.bv_nat 16 65535)));
      v_6997 <- getRegister v_3391;
      v_6999 <- eval (add (mux v_6991 v_6994 (add v_6994 (expression.bv_nat 17 1))) (concat (expression.bv_nat 1 0) v_6997));
      v_7000 <- eval (extract v_6999 1 17);
      v_7002 <- eval (isBitSet v_6999 1);
      v_7007 <- eval (eq (bv_xor (extract v_6992 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1));
      setRegister (lhs.of_reg v_3391) v_7000;
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_6992 v_6997) 11) (isBitSet v_6999 12)));
      setRegister cf (isBitClear v_6999 0);
      setRegister of (bit_and (eq v_7007 (isBitSet v_6997 0)) (notBool_ (eq v_7007 v_7002)));
      setRegister pf (parityFlag (extract v_6999 9 17));
      setRegister sf v_7002;
      setRegister zf (zeroFlag v_7000);
      pure ()
    pat_end;
    pattern fun (v_3384 : Mem) (v_3387 : reg (bv 16)) => do
      v_10836 <- getRegister cf;
      v_10837 <- evaluateAddress v_3384;
      v_10838 <- load v_10837 2;
      v_10840 <- eval (concat (expression.bv_nat 1 0) (bv_xor v_10838 (expression.bv_nat 16 65535)));
      v_10843 <- getRegister v_3387;
      v_10845 <- eval (add (mux v_10836 v_10840 (add v_10840 (expression.bv_nat 17 1))) (concat (expression.bv_nat 1 0) v_10843));
      v_10846 <- eval (extract v_10845 1 17);
      v_10848 <- eval (isBitSet v_10845 1);
      v_10853 <- eval (eq (bv_xor (extract v_10838 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1));
      setRegister (lhs.of_reg v_3387) v_10846;
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_10838 v_10843) 11) (isBitSet v_10845 12)));
      setRegister cf (isBitClear v_10845 0);
      setRegister of (bit_and (eq v_10853 (isBitSet v_10843 0)) (notBool_ (eq v_10853 v_10848)));
      setRegister pf (parityFlag (extract v_10845 9 17));
      setRegister sf v_10848;
      setRegister zf (zeroFlag v_10846);
      pure ()
    pat_end;
    pattern fun (v_3374 : imm int) (v_3371 : Mem) => do
      v_13033 <- evaluateAddress v_3371;
      v_13034 <- getRegister cf;
      v_13035 <- eval (handleImmediateWithSignExtend v_3374 16 16);
      v_13037 <- eval (concat (expression.bv_nat 1 0) (bv_xor v_13035 (expression.bv_nat 16 65535)));
      v_13040 <- load v_13033 2;
      v_13042 <- eval (add (mux v_13034 v_13037 (add v_13037 (expression.bv_nat 17 1))) (concat (expression.bv_nat 1 0) v_13040));
      v_13043 <- eval (extract v_13042 1 17);
      store v_13033 v_13043 2;
      v_13046 <- eval (isBitSet v_13042 1);
      v_13051 <- eval (eq (bv_xor (extract v_13035 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1));
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_13035 v_13040) 11) (isBitSet v_13042 12)));
      setRegister cf (isBitClear v_13042 0);
      setRegister of (bit_and (eq v_13051 (isBitSet v_13040 0)) (notBool_ (eq v_13051 v_13046)));
      setRegister pf (parityFlag (extract v_13042 9 17));
      setRegister sf v_13046;
      setRegister zf (zeroFlag v_13043);
      pure ()
    pat_end;
    pattern fun (v_3378 : reg (bv 16)) (v_3375 : Mem) => do
      v_13069 <- evaluateAddress v_3375;
      v_13070 <- getRegister cf;
      v_13071 <- getRegister v_3378;
      v_13073 <- eval (concat (expression.bv_nat 1 0) (bv_xor v_13071 (expression.bv_nat 16 65535)));
      v_13076 <- load v_13069 2;
      v_13078 <- eval (add (mux v_13070 v_13073 (add v_13073 (expression.bv_nat 17 1))) (concat (expression.bv_nat 1 0) v_13076));
      v_13079 <- eval (extract v_13078 1 17);
      store v_13069 v_13079 2;
      v_13082 <- eval (isBitSet v_13078 1);
      v_13087 <- eval (eq (bv_xor (extract v_13071 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1));
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_13071 v_13076) 11) (isBitSet v_13078 12)));
      setRegister cf (isBitClear v_13078 0);
      setRegister of (bit_and (eq v_13087 (isBitSet v_13076 0)) (notBool_ (eq v_13087 v_13082)));
      setRegister pf (parityFlag (extract v_13078 9 17));
      setRegister sf v_13082;
      setRegister zf (zeroFlag v_13079);
      pure ()
    pat_end
