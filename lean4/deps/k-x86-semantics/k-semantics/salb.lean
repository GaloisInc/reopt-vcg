def salb1 : instruction :=
  definst "salb" $ do
    pattern fun (_ : clReg) (mem_0 : Mem) => do
      v_1 <- evaluateAddress mem_0;
      v_2 <- load v_1 1;
      v_3 <- getRegister rcx;
      v_4 <- eval (bv_and (extract v_3 56 64) (expression.bv_nat 8 31));
      v_5 <- eval (extract (shl (concat (expression.bv_nat 1 0) v_2) (concat (expression.bv_nat 1 0) v_4)) 0 9);
      v_6 <- eval (extract v_5 1 9);
      store v_1 v_6 1;
      v_8 <- eval (eq v_4 (expression.bv_nat 8 0));
      v_9 <- getRegister zf;
      v_10 <- getRegister sf;
      v_11 <- eval (isBitSet v_5 1);
      v_12 <- getRegister pf;
      v_13 <- getRegister cf;
      v_14 <- eval (mux (uge v_4 (expression.bv_nat 8 8)) undef (mux v_8 v_13 (isBitSet v_5 0)));
      v_15 <- getRegister of;
      v_16 <- getRegister af;
      setRegister af (mux v_8 v_16 undef);
      setRegister cf v_14;
      setRegister of (mux (eq v_4 (expression.bv_nat 8 1)) (notBool_ (eq v_14 v_11)) (mux v_8 v_15 undef));
      setRegister pf (mux v_8 v_12 (parityFlag v_6));
      setRegister sf (mux v_8 v_10 v_11);
      setRegister zf (mux v_8 v_9 (eq v_6 (expression.bv_nat 8 0)));
      pure ()
    pat_end;
    pattern fun (_ : clReg) (rh_0 : reg (bv 8)) => do
      v_1 <- getRegister rcx;
      v_2 <- eval (bv_and (extract v_1 56 64) (expression.bv_nat 8 31));
      v_3 <- eval (eq v_2 (expression.bv_nat 8 0));
      v_4 <- getRegister zf;
      v_5 <- getRegister rh_0;
      v_6 <- eval (extract (shl (concat (expression.bv_nat 1 0) v_5) (concat (expression.bv_nat 1 0) v_2)) 0 9);
      v_7 <- eval (extract v_6 1 9);
      v_8 <- getRegister sf;
      v_9 <- eval (isBitSet v_6 1);
      v_10 <- getRegister pf;
      v_11 <- getRegister cf;
      v_12 <- eval (mux (uge v_2 (expression.bv_nat 8 8)) undef (mux v_3 v_11 (isBitSet v_6 0)));
      v_13 <- getRegister of;
      v_14 <- getRegister af;
      setRegister (lhs.of_reg rh_0) v_7;
      setRegister af (mux v_3 v_14 undef);
      setRegister cf v_12;
      setRegister of (mux (eq v_2 (expression.bv_nat 8 1)) (notBool_ (eq v_12 v_9)) (mux v_3 v_13 undef));
      setRegister pf (mux v_3 v_10 (parityFlag v_7));
      setRegister sf (mux v_3 v_8 v_9);
      setRegister zf (mux v_3 v_4 (eq v_7 (expression.bv_nat 8 0)));
      pure ()
    pat_end;
    pattern fun (imm_0 : imm int) (mem_1 : Mem) => do
      v_2 <- evaluateAddress mem_1;
      v_3 <- load v_2 1;
      v_4 <- eval (bv_and (handleImmediateWithSignExtend imm_0 8 8) (expression.bv_nat 8 31));
      v_5 <- eval (extract (shl (concat (expression.bv_nat 1 0) v_3) (concat (expression.bv_nat 1 0) v_4)) 0 9);
      v_6 <- eval (extract v_5 1 9);
      store v_2 v_6 1;
      v_8 <- eval (eq v_4 (expression.bv_nat 8 0));
      v_9 <- getRegister zf;
      v_10 <- getRegister sf;
      v_11 <- eval (isBitSet v_5 1);
      v_12 <- getRegister pf;
      v_13 <- getRegister cf;
      v_14 <- eval (mux (uge v_4 (expression.bv_nat 8 8)) undef (mux v_8 v_13 (isBitSet v_5 0)));
      v_15 <- getRegister of;
      v_16 <- getRegister af;
      setRegister af (mux v_8 v_16 undef);
      setRegister cf v_14;
      setRegister of (mux (eq v_4 (expression.bv_nat 8 1)) (notBool_ (eq v_14 v_11)) (mux v_8 v_15 undef));
      setRegister pf (mux v_8 v_12 (parityFlag v_6));
      setRegister sf (mux v_8 v_10 v_11);
      setRegister zf (mux v_8 v_9 (eq v_6 (expression.bv_nat 8 0)));
      pure ()
    pat_end;
    pattern fun (imm_0 : imm int) (rh_1 : reg (bv 8)) => do
      v_2 <- eval (bv_and (handleImmediateWithSignExtend imm_0 8 8) (expression.bv_nat 8 31));
      v_3 <- eval (eq v_2 (expression.bv_nat 8 0));
      v_4 <- getRegister zf;
      v_5 <- getRegister rh_1;
      v_6 <- eval (extract (shl (concat (expression.bv_nat 1 0) v_5) (concat (expression.bv_nat 1 0) v_2)) 0 9);
      v_7 <- eval (extract v_6 1 9);
      v_8 <- getRegister sf;
      v_9 <- eval (isBitSet v_6 1);
      v_10 <- getRegister pf;
      v_11 <- getRegister cf;
      v_12 <- eval (mux (uge v_2 (expression.bv_nat 8 8)) undef (mux v_3 v_11 (isBitSet v_6 0)));
      v_13 <- getRegister of;
      v_14 <- getRegister af;
      setRegister (lhs.of_reg rh_1) v_7;
      setRegister af (mux v_3 v_14 undef);
      setRegister cf v_12;
      setRegister of (mux (eq v_2 (expression.bv_nat 8 1)) (notBool_ (eq v_12 v_9)) (mux v_3 v_13 undef));
      setRegister pf (mux v_3 v_10 (parityFlag v_7));
      setRegister sf (mux v_3 v_8 v_9);
      setRegister zf (mux v_3 v_4 (eq v_7 (expression.bv_nat 8 0)));
      pure ()
    pat_end;
    pattern fun (mem_0 : Mem) => do
      v_1 <- evaluateAddress mem_0;
      v_2 <- load v_1 1;
      v_3 <- eval (extract (shl (concat (expression.bv_nat 1 0) v_2) (expression.bv_nat 9 1)) 0 9);
      v_4 <- eval (extract v_3 1 9);
      store v_1 v_4 1;
      v_6 <- eval (isBitSet v_3 1);
      v_7 <- eval (isBitSet v_3 0);
      setRegister af undef;
      setRegister cf v_7;
      setRegister of (notBool_ (eq v_7 v_6));
      setRegister pf (parityFlag v_4);
      setRegister sf v_6;
      setRegister zf (zeroFlag v_4);
      pure ()
    pat_end;
    pattern fun (rh_0 : reg (bv 8)) => do
      v_1 <- getRegister rh_0;
      v_2 <- eval (extract (shl (concat (expression.bv_nat 1 0) v_1) (expression.bv_nat 9 1)) 0 9);
      v_3 <- eval (extract v_2 1 9);
      v_4 <- eval (isBitSet v_2 1);
      v_5 <- eval (isBitSet v_2 0);
      setRegister (lhs.of_reg rh_0) v_3;
      setRegister af undef;
      setRegister cf v_5;
      setRegister of (notBool_ (eq v_5 v_4));
      setRegister pf (parityFlag v_3);
      setRegister sf v_4;
      setRegister zf (zeroFlag v_3);
      pure ()
    pat_end
