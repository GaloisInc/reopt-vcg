def rcll1 : instruction :=
  definst "rcll" $ do
    pattern fun (_ : clReg) (mem_0 : Mem) => do
      v_1 <- evaluateAddress mem_0;
      v_2 <- getRegister cf;
      v_3 <- load v_1 4;
      v_4 <- getRegister rcx;
      v_5 <- eval (urem (concat (expression.bv_nat 25 0) (bv_and (extract v_4 56 64) (expression.bv_nat 8 31))) (expression.bv_nat 33 33));
      v_6 <- eval (rol (concat (mux v_2 (expression.bv_nat 1 1) (expression.bv_nat 1 0)) v_3) v_5);
      store v_1 (extract v_6 1 33) 4;
      v_8 <- eval (extract v_5 25 33);
      v_9 <- eval (isBitSet v_6 0);
      v_10 <- getRegister of;
      setRegister cf v_9;
      setRegister of (mux (eq v_8 (expression.bv_nat 8 1)) (notBool_ (eq v_9 (isBitSet v_6 1))) (mux (eq v_8 (expression.bv_nat 8 0)) v_10 undef));
      pure ()
    pat_end;
    pattern fun (_ : clReg) (r32_0 : reg (bv 32)) => do
      v_1 <- getRegister rcx;
      v_2 <- eval (urem (concat (expression.bv_nat 25 0) (bv_and (extract v_1 56 64) (expression.bv_nat 8 31))) (expression.bv_nat 33 33));
      v_3 <- eval (extract v_2 25 33);
      v_4 <- getRegister cf;
      v_5 <- getRegister r32_0;
      v_6 <- eval (rol (concat (mux v_4 (expression.bv_nat 1 1) (expression.bv_nat 1 0)) v_5) v_2);
      v_7 <- eval (isBitSet v_6 0);
      v_8 <- getRegister of;
      setRegister (lhs.of_reg r32_0) (extract v_6 1 33);
      setRegister cf v_7;
      setRegister of (mux (eq v_3 (expression.bv_nat 8 1)) (notBool_ (eq v_7 (isBitSet v_6 1))) (mux (eq v_3 (expression.bv_nat 8 0)) v_8 undef));
      pure ()
    pat_end;
    pattern fun (imm_0 : imm int) (mem_1 : Mem) => do
      v_2 <- evaluateAddress mem_1;
      v_3 <- getRegister cf;
      v_4 <- load v_2 4;
      v_5 <- eval (urem (concat (expression.bv_nat 25 0) (bv_and (handleImmediateWithSignExtend imm_0 8 8) (expression.bv_nat 8 31))) (expression.bv_nat 33 33));
      v_6 <- eval (rol (concat (mux v_3 (expression.bv_nat 1 1) (expression.bv_nat 1 0)) v_4) v_5);
      store v_2 (extract v_6 1 33) 4;
      v_8 <- eval (extract v_5 25 33);
      v_9 <- eval (isBitSet v_6 0);
      v_10 <- getRegister of;
      setRegister cf v_9;
      setRegister of (mux (eq v_8 (expression.bv_nat 8 1)) (notBool_ (eq v_9 (isBitSet v_6 1))) (mux (eq v_8 (expression.bv_nat 8 0)) v_10 undef));
      pure ()
    pat_end;
    pattern fun (imm_0 : imm int) (r32_1 : reg (bv 32)) => do
      v_2 <- eval (urem (concat (expression.bv_nat 25 0) (bv_and (handleImmediateWithSignExtend imm_0 8 8) (expression.bv_nat 8 31))) (expression.bv_nat 33 33));
      v_3 <- eval (extract v_2 25 33);
      v_4 <- getRegister cf;
      v_5 <- getRegister r32_1;
      v_6 <- eval (rol (concat (mux v_4 (expression.bv_nat 1 1) (expression.bv_nat 1 0)) v_5) v_2);
      v_7 <- eval (isBitSet v_6 0);
      v_8 <- getRegister of;
      setRegister (lhs.of_reg r32_1) (extract v_6 1 33);
      setRegister cf v_7;
      setRegister of (mux (eq v_3 (expression.bv_nat 8 1)) (notBool_ (eq v_7 (isBitSet v_6 1))) (mux (eq v_3 (expression.bv_nat 8 0)) v_8 undef));
      pure ()
    pat_end
