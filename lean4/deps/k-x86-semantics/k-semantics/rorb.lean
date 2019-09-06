def rorb1 : instruction :=
  definst "rorb" $ do
    pattern fun (_ : clReg) (v_2772 : reg (bv 8)) => do
      v_4940 <- getRegister rcx;
      v_4942 <- eval (bv_and (extract v_4940 56 64) (expression.bv_nat 8 31));
      v_4944 <- getRegister v_2772;
      v_4945 <- eval (ror v_4944 v_4942);
      v_4946 <- eval (isBitSet v_4945 0);
      v_4950 <- eval (eq v_4942 (expression.bv_nat 8 0));
      v_4951 <- getRegister of;
      v_4954 <- getRegister cf;
      setRegister (lhs.of_reg v_2772) v_4945;
      setRegister cf (mux v_4950 v_4954 v_4946);
      setRegister of (mux (eq v_4942 (expression.bv_nat 8 1)) (notBool_ (eq v_4946 (isBitSet v_4945 1))) (mux v_4950 v_4951 undef));
      pure ()
    pat_end;
    pattern fun (v_2773 : imm int) (v_2777 : reg (bv 8)) => do
      v_4960 <- eval (bv_and (handleImmediateWithSignExtend v_2773 8 8) (expression.bv_nat 8 31));
      v_4962 <- getRegister v_2777;
      v_4963 <- eval (ror v_4962 v_4960);
      v_4964 <- eval (isBitSet v_4963 0);
      v_4968 <- eval (eq v_4960 (expression.bv_nat 8 0));
      v_4969 <- getRegister of;
      v_4972 <- getRegister cf;
      setRegister (lhs.of_reg v_2777) v_4963;
      setRegister cf (mux v_4968 v_4972 v_4964);
      setRegister of (mux (eq v_4960 (expression.bv_nat 8 1)) (notBool_ (eq v_4964 (isBitSet v_4963 1))) (mux v_4968 v_4969 undef));
      pure ()
    pat_end;
    pattern fun (_ : clReg) (v_2746 : Mem) => do
      v_11593 <- evaluateAddress v_2746;
      v_11594 <- load v_11593 1;
      v_11595 <- getRegister rcx;
      v_11597 <- eval (bv_and (extract v_11595 56 64) (expression.bv_nat 8 31));
      v_11598 <- eval (ror v_11594 v_11597);
      store v_11593 v_11598 1;
      v_11601 <- eval (isBitSet v_11598 0);
      v_11605 <- eval (eq v_11597 (expression.bv_nat 8 0));
      v_11606 <- getRegister of;
      v_11609 <- getRegister cf;
      setRegister cf (mux v_11605 v_11609 v_11601);
      setRegister of (mux (eq v_11597 (expression.bv_nat 8 1)) (notBool_ (eq v_11601 (isBitSet v_11598 1))) (mux v_11605 v_11606 undef));
      pure ()
    pat_end;
    pattern fun (v_2749 : imm int) (v_2750 : Mem) => do
      v_11613 <- evaluateAddress v_2750;
      v_11614 <- load v_11613 1;
      v_11616 <- eval (bv_and (handleImmediateWithSignExtend v_2749 8 8) (expression.bv_nat 8 31));
      v_11617 <- eval (ror v_11614 v_11616);
      store v_11613 v_11617 1;
      v_11620 <- eval (isBitSet v_11617 0);
      v_11624 <- eval (eq v_11616 (expression.bv_nat 8 0));
      v_11625 <- getRegister of;
      v_11628 <- getRegister cf;
      setRegister cf (mux v_11624 v_11628 v_11620);
      setRegister of (mux (eq v_11616 (expression.bv_nat 8 1)) (notBool_ (eq v_11620 (isBitSet v_11617 1))) (mux v_11624 v_11625 undef));
      pure ()
    pat_end
