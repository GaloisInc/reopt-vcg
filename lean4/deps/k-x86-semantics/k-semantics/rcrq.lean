def rcrq1 : instruction :=
  definst "rcrq" $ do
    pattern fun (_ : clReg) (v_2602 : reg (bv 64)) => do
      v_4464 <- getRegister rcx;
      v_4468 <- eval (urem (concat (expression.bv_nat 57 0) (bv_and (extract v_4464 56 64) (expression.bv_nat 8 63))) (expression.bv_nat 65 65));
      v_4469 <- eval (extract v_4468 57 65);
      v_4471 <- getRegister cf;
      v_4473 <- getRegister v_2602;
      v_4475 <- eval (ror (concat (mux v_4471 (expression.bv_nat 1 1) (expression.bv_nat 1 0)) v_4473) v_4468);
      v_4481 <- getRegister of;
      setRegister (lhs.of_reg v_2602) (extract v_4475 1 65);
      setRegister cf (isBitSet v_4475 0);
      setRegister of (mux (eq v_4469 (expression.bv_nat 8 1)) (notBool_ (eq (isBitSet v_4475 1) (isBitSet v_4475 2))) (mux (eq v_4469 (expression.bv_nat 8 0)) v_4481 undef));
      pure ()
    pat_end;
    pattern fun (v_2607 : imm int) (v_2606 : reg (bv 64)) => do
      v_4492 <- eval (urem (concat (expression.bv_nat 57 0) (bv_and (handleImmediateWithSignExtend v_2607 8 8) (expression.bv_nat 8 63))) (expression.bv_nat 65 65));
      v_4493 <- eval (extract v_4492 57 65);
      v_4495 <- getRegister cf;
      v_4497 <- getRegister v_2606;
      v_4499 <- eval (ror (concat (mux v_4495 (expression.bv_nat 1 1) (expression.bv_nat 1 0)) v_4497) v_4492);
      v_4505 <- getRegister of;
      setRegister (lhs.of_reg v_2606) (extract v_4499 1 65);
      setRegister cf (isBitSet v_4499 0);
      setRegister of (mux (eq v_4493 (expression.bv_nat 8 1)) (notBool_ (eq (isBitSet v_4499 1) (isBitSet v_4499 2))) (mux (eq v_4493 (expression.bv_nat 8 0)) v_4505 undef));
      pure ()
    pat_end;
    pattern fun (_ : clReg) (v_2592 : Mem) => do
      v_11188 <- evaluateAddress v_2592;
      v_11189 <- getRegister cf;
      v_11191 <- load v_11188 8;
      v_11193 <- getRegister rcx;
      v_11197 <- eval (urem (concat (expression.bv_nat 57 0) (bv_and (extract v_11193 56 64) (expression.bv_nat 8 63))) (expression.bv_nat 65 65));
      v_11198 <- eval (ror (concat (mux v_11189 (expression.bv_nat 1 1) (expression.bv_nat 1 0)) v_11191) v_11197);
      store v_11188 (extract v_11198 1 65) 8;
      v_11201 <- eval (extract v_11197 57 65);
      v_11208 <- getRegister of;
      setRegister cf (isBitSet v_11198 0);
      setRegister of (mux (eq v_11201 (expression.bv_nat 8 1)) (notBool_ (eq (isBitSet v_11198 1) (isBitSet v_11198 2))) (mux (eq v_11201 (expression.bv_nat 8 0)) v_11208 undef));
      pure ()
    pat_end;
    pattern fun (v_2595 : imm int) (v_2596 : Mem) => do
      v_11214 <- evaluateAddress v_2596;
      v_11215 <- getRegister cf;
      v_11217 <- load v_11214 8;
      v_11222 <- eval (urem (concat (expression.bv_nat 57 0) (bv_and (handleImmediateWithSignExtend v_2595 8 8) (expression.bv_nat 8 63))) (expression.bv_nat 65 65));
      v_11223 <- eval (ror (concat (mux v_11215 (expression.bv_nat 1 1) (expression.bv_nat 1 0)) v_11217) v_11222);
      store v_11214 (extract v_11223 1 65) 8;
      v_11226 <- eval (extract v_11222 57 65);
      v_11233 <- getRegister of;
      setRegister cf (isBitSet v_11223 0);
      setRegister of (mux (eq v_11226 (expression.bv_nat 8 1)) (notBool_ (eq (isBitSet v_11223 1) (isBitSet v_11223 2))) (mux (eq v_11226 (expression.bv_nat 8 0)) v_11233 undef));
      pure ()
    pat_end
