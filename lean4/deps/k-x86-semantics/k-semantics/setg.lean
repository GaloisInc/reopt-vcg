def setg1 : instruction :=
  definst "setg" $ do
    pattern fun (v_2449 : reg (bv 8)) => do
      v_3915 <- getRegister zf;
      v_3918 <- getRegister sf;
      v_3920 <- getRegister of;
      setRegister (lhs.of_reg v_2449) (mux (bit_and (notBool_ (eq v_3915 (expression.bv_nat 1 1))) (eq (eq v_3918 (expression.bv_nat 1 1)) (eq v_3920 (expression.bv_nat 1 1)))) (expression.bv_nat 8 1) (expression.bv_nat 8 0));
      pure ()
    pat_end;
    pattern fun (v_2445 : Mem) => do
      v_9442 <- evaluateAddress v_2445;
      v_9443 <- getRegister zf;
      v_9446 <- getRegister sf;
      v_9448 <- getRegister of;
      store v_9442 (mux (bit_and (notBool_ (eq v_9443 (expression.bv_nat 1 1))) (eq (eq v_9446 (expression.bv_nat 1 1)) (eq v_9448 (expression.bv_nat 1 1)))) (expression.bv_nat 8 1) (expression.bv_nat 8 0)) 1;
      pure ()
    pat_end
