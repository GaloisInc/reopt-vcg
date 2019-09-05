def setc1 : instruction :=
  definst "setc" $ do
    pattern fun (v_2495 : reg (bv 8)) => do
      v_3961 <- getRegister cf;
      setRegister (lhs.of_reg v_2495) (mux (eq v_3961 (expression.bv_nat 1 1)) (expression.bv_nat 8 1) (expression.bv_nat 8 0));
      pure ()
    pat_end;
    pattern fun (v_2487 : Mem) => do
      v_8479 <- evaluateAddress v_2487;
      v_8480 <- getRegister cf;
      store v_8479 (mux (eq v_8480 (expression.bv_nat 1 1)) (expression.bv_nat 8 1) (expression.bv_nat 8 0)) 1;
      pure ()
    pat_end
