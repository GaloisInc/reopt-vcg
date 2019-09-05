def setpo1 : instruction :=
  definst "setpo" $ do
    pattern fun (v_2748 : reg (bv 8)) => do
      v_4329 <- getRegister pf;
      setRegister (lhs.of_reg v_2748) (mux (notBool_ (eq v_4329 (expression.bv_nat 1 1))) (expression.bv_nat 8 1) (expression.bv_nat 8 0));
      pure ()
    pat_end;
    pattern fun (v_2740 : Mem) => do
      v_8651 <- evaluateAddress v_2740;
      v_8652 <- getRegister pf;
      store v_8651 (mux (notBool_ (eq v_8652 (expression.bv_nat 1 1))) (expression.bv_nat 8 1) (expression.bv_nat 8 0)) 1;
      pure ()
    pat_end
