def rorq : instruction :=
  definst "rorq" $ do
    pattern fun (_ : clReg) (mem_0 : Mem) => do
      v_1 <- evaluateAddress mem_0;
      v_2 <- load v_1 8;
      v_3 <- getRegister rcx;
      v_4 <- eval (bv_and (extract v_3 56 64) (expression.bv_nat 8 63));
      v_5 <- eval (ror v_2 (concat (expression.bv_nat 56 0) v_4));
      store v_1 v_5 8;
      v_7 <- eval (isBitSet v_5 0);
      v_8 <- eval (eq v_4 (expression.bv_nat 8 0));
      v_9 <- getRegister of;
      v_10 <- getRegister cf;
      setRegister cf (mux v_8 v_10 v_7);
      setRegister of (mux (eq v_4 (expression.bv_nat 8 1)) (notBool_ (eq v_7 (isBitSet v_5 1))) (mux v_8 v_9 undef));
      pure ()
    pat_end;
    pattern fun (_ : clReg) (r64_0 : reg (bv 64)) => do
      v_1 <- getRegister rcx;
      v_2 <- eval (bv_and (extract v_1 56 64) (expression.bv_nat 8 63));
      v_3 <- getRegister (lhs.of_reg r64_0);
      v_4 <- eval (ror v_3 (concat (expression.bv_nat 56 0) v_2));
      v_5 <- eval (isBitSet v_4 0);
      v_6 <- eval (eq v_2 (expression.bv_nat 8 0));
      v_7 <- getRegister of;
      v_8 <- getRegister cf;
      setRegister (lhs.of_reg r64_0) v_4;
      setRegister cf (mux v_6 v_8 v_5);
      setRegister of (mux (eq v_2 (expression.bv_nat 8 1)) (notBool_ (eq v_5 (isBitSet v_4 1))) (mux v_6 v_7 undef));
      pure ()
    pat_end;
    pattern fun (imm_0 : imm int) (mem_1 : Mem) => do
      v_2 <- evaluateAddress mem_1;
      v_3 <- load v_2 8;
      v_4 <- eval (bv_and (handleImmediateWithSignExtend imm_0 8 8) (expression.bv_nat 8 63));
      v_5 <- eval (ror v_3 (concat (expression.bv_nat 56 0) v_4));
      store v_2 v_5 8;
      v_7 <- eval (isBitSet v_5 0);
      v_8 <- eval (eq v_4 (expression.bv_nat 8 0));
      v_9 <- getRegister of;
      v_10 <- getRegister cf;
      setRegister cf (mux v_8 v_10 v_7);
      setRegister of (mux (eq v_4 (expression.bv_nat 8 1)) (notBool_ (eq v_7 (isBitSet v_5 1))) (mux v_8 v_9 undef));
      pure ()
    pat_end;
    pattern fun (imm_0 : imm int) (r64_1 : reg (bv 64)) => do
      v_2 <- eval (bv_and (handleImmediateWithSignExtend imm_0 8 8) (expression.bv_nat 8 63));
      v_3 <- getRegister (lhs.of_reg r64_1);
      v_4 <- eval (ror v_3 (concat (expression.bv_nat 56 0) v_2));
      v_5 <- eval (isBitSet v_4 0);
      v_6 <- eval (eq v_2 (expression.bv_nat 8 0));
      v_7 <- getRegister of;
      v_8 <- getRegister cf;
      setRegister (lhs.of_reg r64_1) v_4;
      setRegister cf (mux v_6 v_8 v_5);
      setRegister of (mux (eq v_2 (expression.bv_nat 8 1)) (notBool_ (eq v_5 (isBitSet v_4 1))) (mux v_6 v_7 undef));
      pure ()
    pat_end
