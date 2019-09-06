def rcrl1 : instruction :=
  definst "rcrl" $ do
    pattern fun (_ : clReg) (v_2581 : reg (bv 32)) => do
      v_4391 <- getRegister rcx;
      v_4395 <- eval (urem (concat (expression.bv_nat 25 0) (bv_and (extract v_4391 56 64) (expression.bv_nat 8 31))) (expression.bv_nat 33 33));
      v_4396 <- eval (extract v_4395 25 33);
      v_4398 <- getRegister cf;
      v_4400 <- getRegister v_2581;
      v_4402 <- eval (ror (concat (mux v_4398 (expression.bv_nat 1 1) (expression.bv_nat 1 0)) v_4400) v_4395);
      v_4408 <- getRegister of;
      setRegister (lhs.of_reg v_2581) (extract v_4402 1 33);
      setRegister cf (isBitSet v_4402 0);
      setRegister of (mux (eq v_4396 (expression.bv_nat 8 1)) (notBool_ (eq (isBitSet v_4402 1) (isBitSet v_4402 2))) (mux (eq v_4396 (expression.bv_nat 8 0)) v_4408 undef));
      pure ()
    pat_end;
    pattern fun (v_2583 : imm int) (v_2586 : reg (bv 32)) => do
      v_4419 <- eval (urem (concat (expression.bv_nat 25 0) (bv_and (handleImmediateWithSignExtend v_2583 8 8) (expression.bv_nat 8 31))) (expression.bv_nat 33 33));
      v_4420 <- eval (extract v_4419 25 33);
      v_4422 <- getRegister cf;
      v_4424 <- getRegister v_2586;
      v_4426 <- eval (ror (concat (mux v_4422 (expression.bv_nat 1 1) (expression.bv_nat 1 0)) v_4424) v_4419);
      v_4432 <- getRegister of;
      setRegister (lhs.of_reg v_2586) (extract v_4426 1 33);
      setRegister cf (isBitSet v_4426 0);
      setRegister of (mux (eq v_4420 (expression.bv_nat 8 1)) (notBool_ (eq (isBitSet v_4426 1) (isBitSet v_4426 2))) (mux (eq v_4420 (expression.bv_nat 8 0)) v_4432 undef));
      pure ()
    pat_end;
    pattern fun (_ : clReg) (v_2569 : Mem) => do
      v_11107 <- evaluateAddress v_2569;
      v_11108 <- getRegister cf;
      v_11110 <- load v_11107 4;
      v_11112 <- getRegister rcx;
      v_11116 <- eval (urem (concat (expression.bv_nat 25 0) (bv_and (extract v_11112 56 64) (expression.bv_nat 8 31))) (expression.bv_nat 33 33));
      v_11117 <- eval (ror (concat (mux v_11108 (expression.bv_nat 1 1) (expression.bv_nat 1 0)) v_11110) v_11116);
      store v_11107 (extract v_11117 1 33) 4;
      v_11120 <- eval (extract v_11116 25 33);
      v_11127 <- getRegister of;
      setRegister cf (isBitSet v_11117 0);
      setRegister of (mux (eq v_11120 (expression.bv_nat 8 1)) (notBool_ (eq (isBitSet v_11117 1) (isBitSet v_11117 2))) (mux (eq v_11120 (expression.bv_nat 8 0)) v_11127 undef));
      pure ()
    pat_end;
    pattern fun (v_2572 : imm int) (v_2573 : Mem) => do
      v_11133 <- evaluateAddress v_2573;
      v_11134 <- getRegister cf;
      v_11136 <- load v_11133 4;
      v_11141 <- eval (urem (concat (expression.bv_nat 25 0) (bv_and (handleImmediateWithSignExtend v_2572 8 8) (expression.bv_nat 8 31))) (expression.bv_nat 33 33));
      v_11142 <- eval (ror (concat (mux v_11134 (expression.bv_nat 1 1) (expression.bv_nat 1 0)) v_11136) v_11141);
      store v_11133 (extract v_11142 1 33) 4;
      v_11145 <- eval (extract v_11141 25 33);
      v_11152 <- getRegister of;
      setRegister cf (isBitSet v_11142 0);
      setRegister of (mux (eq v_11145 (expression.bv_nat 8 1)) (notBool_ (eq (isBitSet v_11142 1) (isBitSet v_11142 2))) (mux (eq v_11145 (expression.bv_nat 8 0)) v_11152 undef));
      pure ()
    pat_end
