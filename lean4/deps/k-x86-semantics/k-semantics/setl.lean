def setl1 : instruction :=
  definst "setl" $ do
    pattern fun (v_2539 : reg (bv 8)) => do
      v_4029 <- getRegister sf;
      v_4031 <- getRegister of;
      setRegister (lhs.of_reg v_2539) (mux (notBool_ (eq (eq v_4029 (expression.bv_nat 1 1)) (eq v_4031 (expression.bv_nat 1 1)))) (expression.bv_nat 8 1) (expression.bv_nat 8 0));
      pure ()
    pat_end;
    pattern fun (v_2531 : Mem) => do
      v_8509 <- evaluateAddress v_2531;
      v_8510 <- getRegister sf;
      v_8512 <- getRegister of;
      store v_8509 (mux (notBool_ (eq (eq v_8510 (expression.bv_nat 1 1)) (eq v_8512 (expression.bv_nat 1 1)))) (expression.bv_nat 8 1) (expression.bv_nat 8 0)) 1;
      pure ()
    pat_end
