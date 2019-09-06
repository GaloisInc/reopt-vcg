def rolb1 : instruction :=
  definst "rolb" $ do
    pattern fun (_ : clReg) (v_2664 : reg (bv 8)) => do
      v_4656 <- getRegister rcx;
      v_4658 <- eval (bv_and (extract v_4656 56 64) (expression.bv_nat 8 31));
      v_4660 <- getRegister v_2664;
      v_4661 <- eval (rol v_4660 v_4658);
      v_4663 <- eval (isBitSet v_4661 7);
      v_4666 <- eval (eq v_4658 (expression.bv_nat 8 0));
      v_4667 <- getRegister of;
      v_4670 <- getRegister cf;
      setRegister (lhs.of_reg v_2664) v_4661;
      setRegister cf (mux v_4666 v_4670 v_4663);
      setRegister of (mux (eq v_4658 (expression.bv_nat 8 1)) (notBool_ (eq (isBitSet v_4661 0) v_4663)) (mux v_4666 v_4667 undef));
      pure ()
    pat_end;
    pattern fun (v_2665 : imm int) (v_2669 : reg (bv 8)) => do
      v_4676 <- eval (bv_and (handleImmediateWithSignExtend v_2665 8 8) (expression.bv_nat 8 31));
      v_4678 <- getRegister v_2669;
      v_4679 <- eval (rol v_4678 v_4676);
      v_4681 <- eval (isBitSet v_4679 7);
      v_4684 <- eval (eq v_4676 (expression.bv_nat 8 0));
      v_4685 <- getRegister of;
      v_4688 <- getRegister cf;
      setRegister (lhs.of_reg v_2669) v_4679;
      setRegister cf (mux v_4684 v_4688 v_4681);
      setRegister of (mux (eq v_4676 (expression.bv_nat 8 1)) (notBool_ (eq (isBitSet v_4679 0) v_4681)) (mux v_4684 v_4685 undef));
      pure ()
    pat_end;
    pattern fun (_ : clReg) (v_2638 : Mem) => do
      v_11350 <- evaluateAddress v_2638;
      v_11351 <- load v_11350 1;
      v_11352 <- getRegister rcx;
      v_11354 <- eval (bv_and (extract v_11352 56 64) (expression.bv_nat 8 31));
      v_11355 <- eval (rol v_11351 v_11354);
      store v_11350 v_11355 1;
      v_11359 <- eval (isBitSet v_11355 7);
      v_11362 <- eval (eq v_11354 (expression.bv_nat 8 0));
      v_11363 <- getRegister of;
      v_11366 <- getRegister cf;
      setRegister cf (mux v_11362 v_11366 v_11359);
      setRegister of (mux (eq v_11354 (expression.bv_nat 8 1)) (notBool_ (eq (isBitSet v_11355 0) v_11359)) (mux v_11362 v_11363 undef));
      pure ()
    pat_end;
    pattern fun (v_2641 : imm int) (v_2642 : Mem) => do
      v_11370 <- evaluateAddress v_2642;
      v_11371 <- load v_11370 1;
      v_11373 <- eval (bv_and (handleImmediateWithSignExtend v_2641 8 8) (expression.bv_nat 8 31));
      v_11374 <- eval (rol v_11371 v_11373);
      store v_11370 v_11374 1;
      v_11378 <- eval (isBitSet v_11374 7);
      v_11381 <- eval (eq v_11373 (expression.bv_nat 8 0));
      v_11382 <- getRegister of;
      v_11385 <- getRegister cf;
      setRegister cf (mux v_11381 v_11385 v_11378);
      setRegister of (mux (eq v_11373 (expression.bv_nat 8 1)) (notBool_ (eq (isBitSet v_11374 0) v_11378)) (mux v_11381 v_11382 undef));
      pure ()
    pat_end
