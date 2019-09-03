def setc1 : instruction :=
  definst "setc" $ do
    pattern fun (v_2440 : reg (bv 8)) => do
      v_3906 <- getRegister cf;
      setRegister (lhs.of_reg v_2440) (mux (eq v_3906 (expression.bv_nat 1 1)) (expression.bv_nat 8 1) (expression.bv_nat 8 0));
      pure ()
    pat_end;
    pattern fun (v_2436 : Mem) => do
      v_9456 <- evaluateAddress v_2436;
      v_9457 <- getRegister cf;
      store v_9456 (mux (eq v_9457 (expression.bv_nat 1 1)) (expression.bv_nat 8 1) (expression.bv_nat 8 0)) 1;
      pure ()
    pat_end
