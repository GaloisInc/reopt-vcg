def setns1 : instruction :=
  definst "setns" $ do
    pattern fun (v_2625 : reg (bv 8)) => do
      v_4201 <- getRegister sf;
      setRegister (lhs.of_reg v_2625) (mux (notBool_ (eq v_4201 (expression.bv_nat 1 1))) (expression.bv_nat 8 1) (expression.bv_nat 8 0));
      pure ()
    pat_end;
    pattern fun (v_2621 : Mem) => do
      v_9577 <- evaluateAddress v_2621;
      v_9578 <- getRegister sf;
      store v_9577 (mux (notBool_ (eq v_9578 (expression.bv_nat 1 1))) (expression.bv_nat 8 1) (expression.bv_nat 8 0)) 1;
      pure ()
    pat_end
