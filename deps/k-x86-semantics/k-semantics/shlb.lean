def shlb : instruction :=
  definst "shlb" $ do
    pattern fun (_ : clReg) (mem_0 : Mem) => do
      v_1 <- evaluateAddress mem_0;
      v_2 <- load v_1 1;
      v_3 <- getRegister rcx;
      (v_4 : expression (bv 8)) <- eval (extract v_3 56 64);
      v_5 <- eval (bv_and v_4 (expression.bv_nat 8 31));
      (v_6 : expression (bv 9)) <- eval (extract (shl (concat (expression.bv_nat 1 0) v_2) (concat (expression.bv_nat 1 0) v_5)) 0 9);
      (v_7 : expression (bv 8)) <- eval (extract v_6 1 9);
      store v_1 v_7 1;
      v_9 <- eval (eq v_5 (expression.bv_nat 8 0));
      v_10 <- getRegister zf;
      v_11 <- getRegister sf;
      v_12 <- eval (isBitSet v_6 1);
      v_13 <- getRegister pf;
      v_14 <- getRegister cf;
      v_15 <- eval (mux (uge v_5 (expression.bv_nat 8 8)) undef (mux v_9 v_14 (isBitSet v_6 0)));
      v_16 <- getRegister of;
      v_17 <- getRegister af;
      setRegister af (mux v_9 v_17 undef);
      setRegister cf v_15;
      setRegister of (mux (eq v_5 (expression.bv_nat 8 1)) (notBool_ (eq v_15 v_12)) (mux v_9 v_16 undef));
      setRegister pf (mux v_9 v_13 (parityFlag v_7));
      setRegister sf (mux v_9 v_11 v_12);
      setRegister zf (mux v_9 v_10 (eq v_7 (expression.bv_nat 8 0)));
      pure ()
    pat_end;
    pattern fun (_ : clReg) (rh_0 : reg (bv 8)) => do
      v_1 <- getRegister rcx;
      (v_2 : expression (bv 8)) <- eval (extract v_1 56 64);
      v_3 <- eval (bv_and v_2 (expression.bv_nat 8 31));
      v_4 <- eval (eq v_3 (expression.bv_nat 8 0));
      v_5 <- getRegister zf;
      v_6 <- getRegister (lhs.of_reg rh_0);
      (v_7 : expression (bv 9)) <- eval (extract (shl (concat (expression.bv_nat 1 0) v_6) (concat (expression.bv_nat 1 0) v_3)) 0 9);
      (v_8 : expression (bv 8)) <- eval (extract v_7 1 9);
      v_9 <- getRegister sf;
      v_10 <- eval (isBitSet v_7 1);
      v_11 <- getRegister pf;
      v_12 <- getRegister cf;
      v_13 <- eval (mux (uge v_3 (expression.bv_nat 8 8)) undef (mux v_4 v_12 (isBitSet v_7 0)));
      v_14 <- getRegister of;
      v_15 <- getRegister af;
      setRegister (lhs.of_reg rh_0) v_8;
      setRegister af (mux v_4 v_15 undef);
      setRegister cf v_13;
      setRegister of (mux (eq v_3 (expression.bv_nat 8 1)) (notBool_ (eq v_13 v_10)) (mux v_4 v_14 undef));
      setRegister pf (mux v_4 v_11 (parityFlag v_8));
      setRegister sf (mux v_4 v_9 v_10);
      setRegister zf (mux v_4 v_5 (eq v_8 (expression.bv_nat 8 0)));
      pure ()
    pat_end;
    pattern fun (imm_0 : imm int) (mem_1 : Mem) => do
      v_2 <- evaluateAddress mem_1;
      v_3 <- load v_2 1;
      v_4 <- eval (bv_and (handleImmediateWithSignExtend imm_0 8 8) (expression.bv_nat 8 31));
      (v_5 : expression (bv 9)) <- eval (extract (shl (concat (expression.bv_nat 1 0) v_3) (concat (expression.bv_nat 1 0) v_4)) 0 9);
      (v_6 : expression (bv 8)) <- eval (extract v_5 1 9);
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
      v_5 <- getRegister (lhs.of_reg rh_1);
      (v_6 : expression (bv 9)) <- eval (extract (shl (concat (expression.bv_nat 1 0) v_5) (concat (expression.bv_nat 1 0) v_2)) 0 9);
      (v_7 : expression (bv 8)) <- eval (extract v_6 1 9);
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
    pat_end
