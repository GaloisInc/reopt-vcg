def setbe1 : instruction :=
  definst "setbe" $ do
    pattern fun (v_2416 : reg (bv 8)) => do
      v_3876 <- getRegister cf;
      v_3878 <- getRegister zf;
      setRegister (lhs.of_reg v_2416) (mux (bit_or (eq v_3876 (expression.bv_nat 1 1)) (eq v_3878 (expression.bv_nat 1 1))) (expression.bv_nat 8 1) (expression.bv_nat 8 0));
      pure ()
    pat_end;
    pattern fun (v_2412 : Mem) => do
      v_9424 <- evaluateAddress v_2412;
      v_9425 <- getRegister cf;
      v_9427 <- getRegister zf;
      store v_9424 (mux (bit_or (eq v_9425 (expression.bv_nat 1 1)) (eq v_9427 (expression.bv_nat 1 1))) (expression.bv_nat 8 1) (expression.bv_nat 8 0)) 1;
      pure ()
    pat_end
