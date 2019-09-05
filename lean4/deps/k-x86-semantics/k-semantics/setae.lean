def setae1 : instruction :=
  definst "setae" $ do
    pattern fun (v_2462 : reg (bv 8)) => do
      v_3921 <- getRegister cf;
      setRegister (lhs.of_reg v_2462) (mux (notBool_ (eq v_3921 (expression.bv_nat 1 1))) (expression.bv_nat 8 1) (expression.bv_nat 8 0));
      pure ()
    pat_end;
    pattern fun (v_2454 : Mem) => do
      v_8460 <- evaluateAddress v_2454;
      v_8461 <- getRegister cf;
      store v_8460 (mux (notBool_ (eq v_8461 (expression.bv_nat 1 1))) (expression.bv_nat 8 1) (expression.bv_nat 8 0)) 1;
      pure ()
    pat_end
