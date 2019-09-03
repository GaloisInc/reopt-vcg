def setpo1 : instruction :=
  definst "setpo" $ do
    pattern fun (v_2680 : reg (bv 8)) => do
      v_4260 <- getRegister pf;
      setRegister (lhs.of_reg v_2680) (mux (notBool_ (eq v_4260 (expression.bv_nat 1 1))) (expression.bv_nat 8 1) (expression.bv_nat 8 0));
      pure ()
    pat_end;
    pattern fun (v_2676 : Mem) => do
      v_9604 <- evaluateAddress v_2676;
      v_9605 <- getRegister pf;
      store v_9604 (mux (notBool_ (eq v_9605 (expression.bv_nat 1 1))) (expression.bv_nat 8 1) (expression.bv_nat 8 0)) 1;
      pure ()
    pat_end
