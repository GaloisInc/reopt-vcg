def rorw : instruction :=
  definst "rorw" $ do
    pattern fun (_ : clReg) (mem_0 : Mem) => do
      v_1 <- evaluateAddress mem_0;
      v_2 <- load v_1 2;
      v_3 <- getRegister rcx;
      (v_4 : expression (bv 8)) <- eval (extract v_3 56 64);
      v_5 <- eval (bv_and v_4 (expression.bv_nat 8 31));
      v_6 <- eval (ror v_2 (concat (expression.bv_nat 8 0) v_5));
      store v_1 v_6 2;
      v_8 <- eval (isBitSet v_6 0);
      v_9 <- eval (eq v_5 (expression.bv_nat 8 0));
      v_10 <- getRegister of;
      v_11 <- getRegister cf;
      setRegister cf (mux v_9 v_11 v_8);
      setRegister of (mux (eq v_5 (expression.bv_nat 8 1)) (notBool_ (eq v_8 (isBitSet v_6 1))) (mux v_9 v_10 undef));
      pure ()
    pat_end;
    pattern fun (_ : clReg) (r16_0 : reg (bv 16)) => do
      v_1 <- getRegister rcx;
      (v_2 : expression (bv 8)) <- eval (extract v_1 56 64);
      v_3 <- eval (bv_and v_2 (expression.bv_nat 8 31));
      v_4 <- getRegister (lhs.of_reg r16_0);
      v_5 <- eval (ror v_4 (concat (expression.bv_nat 8 0) v_3));
      v_6 <- eval (isBitSet v_5 0);
      v_7 <- eval (eq v_3 (expression.bv_nat 8 0));
      v_8 <- getRegister of;
      v_9 <- getRegister cf;
      setRegister (lhs.of_reg r16_0) v_5;
      setRegister cf (mux v_7 v_9 v_6);
      setRegister of (mux (eq v_3 (expression.bv_nat 8 1)) (notBool_ (eq v_6 (isBitSet v_5 1))) (mux v_7 v_8 undef));
      pure ()
    pat_end;
    pattern fun (imm_0 : imm int) (mem_1 : Mem) => do
      v_2 <- evaluateAddress mem_1;
      v_3 <- load v_2 2;
      v_4 <- eval (bv_and (handleImmediateWithSignExtend imm_0 8 8) (expression.bv_nat 8 31));
      v_5 <- eval (ror v_3 (concat (expression.bv_nat 8 0) v_4));
      store v_2 v_5 2;
      v_7 <- eval (isBitSet v_5 0);
      v_8 <- eval (eq v_4 (expression.bv_nat 8 0));
      v_9 <- getRegister of;
      v_10 <- getRegister cf;
      setRegister cf (mux v_8 v_10 v_7);
      setRegister of (mux (eq v_4 (expression.bv_nat 8 1)) (notBool_ (eq v_7 (isBitSet v_5 1))) (mux v_8 v_9 undef));
      pure ()
    pat_end;
    pattern fun (imm_0 : imm int) (r16_1 : reg (bv 16)) => do
      v_2 <- eval (bv_and (handleImmediateWithSignExtend imm_0 8 8) (expression.bv_nat 8 31));
      v_3 <- getRegister (lhs.of_reg r16_1);
      v_4 <- eval (ror v_3 (concat (expression.bv_nat 8 0) v_2));
      v_5 <- eval (isBitSet v_4 0);
      v_6 <- eval (eq v_2 (expression.bv_nat 8 0));
      v_7 <- getRegister of;
      v_8 <- getRegister cf;
      setRegister (lhs.of_reg r16_1) v_4;
      setRegister cf (mux v_6 v_8 v_5);
      setRegister of (mux (eq v_2 (expression.bv_nat 8 1)) (notBool_ (eq v_5 (isBitSet v_4 1))) (mux v_6 v_7 undef));
      pure ()
    pat_end
