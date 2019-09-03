def setna1 : instruction :=
  definst "setna" $ do
    pattern fun (v_2506 : reg (bv 8)) => do
      v_4014 <- getRegister cf;
      v_4016 <- getRegister zf;
      setRegister (lhs.of_reg v_2506) (mux (bit_or (eq v_4014 (expression.bv_nat 1 1)) (eq v_4016 (expression.bv_nat 1 1))) (expression.bv_nat 8 1) (expression.bv_nat 8 0));
      pure ()
    pat_end;
    pattern fun (v_2502 : Mem) => do
      v_9507 <- evaluateAddress v_2502;
      v_9508 <- getRegister cf;
      v_9510 <- getRegister zf;
      store v_9507 (mux (bit_or (eq v_9508 (expression.bv_nat 1 1)) (eq v_9510 (expression.bv_nat 1 1))) (expression.bv_nat 8 1) (expression.bv_nat 8 0)) 1;
      pure ()
    pat_end
