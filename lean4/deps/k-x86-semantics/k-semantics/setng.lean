def setng1 : instruction :=
  definst "setng" $ do
    pattern fun (v_2627 : reg (bv 8)) => do
      v_4164 <- getRegister zf;
      v_4166 <- getRegister sf;
      v_4168 <- getRegister of;
      setRegister (lhs.of_reg v_2627) (mux (bit_or (eq v_4164 (expression.bv_nat 1 1)) (notBool_ (eq (eq v_4166 (expression.bv_nat 1 1)) (eq v_4168 (expression.bv_nat 1 1))))) (expression.bv_nat 8 1) (expression.bv_nat 8 0));
      pure ()
    pat_end;
    pattern fun (v_2619 : Mem) => do
      v_8571 <- evaluateAddress v_2619;
      v_8572 <- getRegister zf;
      v_8574 <- getRegister sf;
      v_8576 <- getRegister of;
      store v_8571 (mux (bit_or (eq v_8572 (expression.bv_nat 1 1)) (notBool_ (eq (eq v_8574 (expression.bv_nat 1 1)) (eq v_8576 (expression.bv_nat 1 1))))) (expression.bv_nat 8 1) (expression.bv_nat 8 0)) 1;
      pure ()
    pat_end
