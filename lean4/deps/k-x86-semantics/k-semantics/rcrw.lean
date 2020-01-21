def rcrw : instruction :=
  definst "rcrw" $ do
    pattern fun (_ : clReg) (mem_0 : Mem) => do
      v_1 <- evaluateAddress mem_0;
      v_2 <- getRegister cf;
      v_3 <- load v_1 2;
      v_4 <- getRegister rcx;
      v_5 <- eval (urem (concat (expression.bv_nat 9 0) (bv_and (extract v_4 56 64) (expression.bv_nat 8 31))) (expression.bv_nat 17 17));
      v_6 <- eval (ror (concat (mux v_2 (expression.bv_nat 1 1) (expression.bv_nat 1 0)) v_3) v_5);
      store v_1 (extract v_6 1 17) 2;
      v_8 <- eval (extract v_5 9 17);
      v_9 <- getRegister of;
      setRegister cf (isBitSet v_6 0);
      setRegister of (mux (eq v_8 (expression.bv_nat 8 1)) (notBool_ (eq (isBitSet v_6 1) (isBitSet v_6 2))) (mux (eq v_8 (expression.bv_nat 8 0)) v_9 undef));
      pure ()
    pat_end;
    pattern fun (_ : clReg) (r16_0 : reg (bv 16)) => do
      v_1 <- getRegister rcx;
      v_2 <- eval (urem (concat (expression.bv_nat 9 0) (bv_and (extract v_1 56 64) (expression.bv_nat 8 31))) (expression.bv_nat 17 17));
      v_3 <- eval (extract v_2 9 17);
      v_4 <- getRegister cf;
      v_5 <- getRegister (lhs.of_reg r16_0);
      v_6 <- eval (ror (concat (mux v_4 (expression.bv_nat 1 1) (expression.bv_nat 1 0)) v_5) v_2);
      v_7 <- getRegister of;
      setRegister (lhs.of_reg r16_0) (extract v_6 1 17);
      setRegister cf (isBitSet v_6 0);
      setRegister of (mux (eq v_3 (expression.bv_nat 8 1)) (notBool_ (eq (isBitSet v_6 1) (isBitSet v_6 2))) (mux (eq v_3 (expression.bv_nat 8 0)) v_7 undef));
      pure ()
    pat_end;
    pattern fun (imm_0 : imm int) (mem_1 : Mem) => do
      v_2 <- evaluateAddress mem_1;
      v_3 <- getRegister cf;
      v_4 <- load v_2 2;
      v_5 <- eval (urem (concat (expression.bv_nat 9 0) (bv_and (handleImmediateWithSignExtend imm_0 8 8) (expression.bv_nat 8 31))) (expression.bv_nat 17 17));
      v_6 <- eval (ror (concat (mux v_3 (expression.bv_nat 1 1) (expression.bv_nat 1 0)) v_4) v_5);
      store v_2 (extract v_6 1 17) 2;
      v_8 <- eval (extract v_5 9 17);
      v_9 <- getRegister of;
      setRegister cf (isBitSet v_6 0);
      setRegister of (mux (eq v_8 (expression.bv_nat 8 1)) (notBool_ (eq (isBitSet v_6 1) (isBitSet v_6 2))) (mux (eq v_8 (expression.bv_nat 8 0)) v_9 undef));
      pure ()
    pat_end;
    pattern fun (imm_0 : imm int) (r16_1 : reg (bv 16)) => do
      v_2 <- eval (urem (concat (expression.bv_nat 9 0) (bv_and (handleImmediateWithSignExtend imm_0 8 8) (expression.bv_nat 8 31))) (expression.bv_nat 17 17));
      v_3 <- eval (extract v_2 9 17);
      v_4 <- getRegister cf;
      v_5 <- getRegister (lhs.of_reg r16_1);
      v_6 <- eval (ror (concat (mux v_4 (expression.bv_nat 1 1) (expression.bv_nat 1 0)) v_5) v_2);
      v_7 <- getRegister of;
      setRegister (lhs.of_reg r16_1) (extract v_6 1 17);
      setRegister cf (isBitSet v_6 0);
      setRegister of (mux (eq v_3 (expression.bv_nat 8 1)) (notBool_ (eq (isBitSet v_6 1) (isBitSet v_6 2))) (mux (eq v_3 (expression.bv_nat 8 0)) v_7 undef));
      pure ()
    pat_end
