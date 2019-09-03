def setl1 : instruction :=
  definst "setl" $ do
    pattern fun (v_2484 : reg (bv 8)) => do
      v_3970 <- getRegister sf;
      v_3972 <- getRegister of;
      setRegister (lhs.of_reg v_2484) (mux (notBool_ (eq (eq v_3970 (expression.bv_nat 1 1)) (eq v_3972 (expression.bv_nat 1 1)))) (expression.bv_nat 8 1) (expression.bv_nat 8 0));
      pure ()
    pat_end;
    pattern fun (v_2480 : Mem) => do
      v_9486 <- evaluateAddress v_2480;
      v_9487 <- getRegister sf;
      v_9489 <- getRegister of;
      store v_9486 (mux (notBool_ (eq (eq v_9487 (expression.bv_nat 1 1)) (eq v_9489 (expression.bv_nat 1 1)))) (expression.bv_nat 8 1) (expression.bv_nat 8 0)) 1;
      pure ()
    pat_end
