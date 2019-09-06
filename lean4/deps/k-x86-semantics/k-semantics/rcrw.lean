def rcrw1 : instruction :=
  definst "rcrw" $ do
    pattern fun (_ : clReg) (v_2627 : reg (bv 16)) => do
      v_4537 <- getRegister rcx;
      v_4541 <- eval (urem (concat (expression.bv_nat 9 0) (bv_and (extract v_4537 56 64) (expression.bv_nat 8 31))) (expression.bv_nat 17 17));
      v_4542 <- eval (extract v_4541 9 17);
      v_4544 <- getRegister cf;
      v_4546 <- getRegister v_2627;
      v_4548 <- eval (ror (concat (mux v_4544 (expression.bv_nat 1 1) (expression.bv_nat 1 0)) v_4546) v_4541);
      v_4554 <- getRegister of;
      setRegister (lhs.of_reg v_2627) (extract v_4548 1 17);
      setRegister cf (isBitSet v_4548 0);
      setRegister of (mux (eq v_4542 (expression.bv_nat 8 1)) (notBool_ (eq (isBitSet v_4548 1) (isBitSet v_4548 2))) (mux (eq v_4542 (expression.bv_nat 8 0)) v_4554 undef));
      pure ()
    pat_end;
    pattern fun (v_2629 : imm int) (v_2632 : reg (bv 16)) => do
      v_4565 <- eval (urem (concat (expression.bv_nat 9 0) (bv_and (handleImmediateWithSignExtend v_2629 8 8) (expression.bv_nat 8 31))) (expression.bv_nat 17 17));
      v_4566 <- eval (extract v_4565 9 17);
      v_4568 <- getRegister cf;
      v_4570 <- getRegister v_2632;
      v_4572 <- eval (ror (concat (mux v_4568 (expression.bv_nat 1 1) (expression.bv_nat 1 0)) v_4570) v_4565);
      v_4578 <- getRegister of;
      setRegister (lhs.of_reg v_2632) (extract v_4572 1 17);
      setRegister cf (isBitSet v_4572 0);
      setRegister of (mux (eq v_4566 (expression.bv_nat 8 1)) (notBool_ (eq (isBitSet v_4572 1) (isBitSet v_4572 2))) (mux (eq v_4566 (expression.bv_nat 8 0)) v_4578 undef));
      pure ()
    pat_end;
    pattern fun (_ : clReg) (v_2615 : Mem) => do
      v_11269 <- evaluateAddress v_2615;
      v_11270 <- getRegister cf;
      v_11272 <- load v_11269 2;
      v_11274 <- getRegister rcx;
      v_11278 <- eval (urem (concat (expression.bv_nat 9 0) (bv_and (extract v_11274 56 64) (expression.bv_nat 8 31))) (expression.bv_nat 17 17));
      v_11279 <- eval (ror (concat (mux v_11270 (expression.bv_nat 1 1) (expression.bv_nat 1 0)) v_11272) v_11278);
      store v_11269 (extract v_11279 1 17) 2;
      v_11282 <- eval (extract v_11278 9 17);
      v_11289 <- getRegister of;
      setRegister cf (isBitSet v_11279 0);
      setRegister of (mux (eq v_11282 (expression.bv_nat 8 1)) (notBool_ (eq (isBitSet v_11279 1) (isBitSet v_11279 2))) (mux (eq v_11282 (expression.bv_nat 8 0)) v_11289 undef));
      pure ()
    pat_end;
    pattern fun (v_2618 : imm int) (v_2619 : Mem) => do
      v_11295 <- evaluateAddress v_2619;
      v_11296 <- getRegister cf;
      v_11298 <- load v_11295 2;
      v_11303 <- eval (urem (concat (expression.bv_nat 9 0) (bv_and (handleImmediateWithSignExtend v_2618 8 8) (expression.bv_nat 8 31))) (expression.bv_nat 17 17));
      v_11304 <- eval (ror (concat (mux v_11296 (expression.bv_nat 1 1) (expression.bv_nat 1 0)) v_11298) v_11303);
      store v_11295 (extract v_11304 1 17) 2;
      v_11307 <- eval (extract v_11303 9 17);
      v_11314 <- getRegister of;
      setRegister cf (isBitSet v_11304 0);
      setRegister of (mux (eq v_11307 (expression.bv_nat 8 1)) (notBool_ (eq (isBitSet v_11304 1) (isBitSet v_11304 2))) (mux (eq v_11307 (expression.bv_nat 8 0)) v_11314 undef));
      pure ()
    pat_end
