def setc1 : instruction :=
  definst "setc" $ do
    pattern fun (v_2427 : reg (bv 8)) => do
      v_3893 <- getRegister cf;
      setRegister (lhs.of_reg v_2427) (mux (eq v_3893 (expression.bv_nat 1 1)) (expression.bv_nat 8 1) (expression.bv_nat 8 0));
      pure ()
    pat_end;
    pattern fun (v_2423 : Mem) => do
      v_9432 <- evaluateAddress v_2423;
      v_9433 <- getRegister cf;
      store v_9432 (mux (eq v_9433 (expression.bv_nat 1 1)) (expression.bv_nat 8 1) (expression.bv_nat 8 0)) 1;
      pure ()
    pat_end
