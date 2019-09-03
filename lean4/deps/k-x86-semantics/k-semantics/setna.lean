def setna1 : instruction :=
  definst "setna" $ do
    pattern fun (v_2493 : reg (bv 8)) => do
      v_4001 <- getRegister cf;
      v_4003 <- getRegister zf;
      setRegister (lhs.of_reg v_2493) (mux (bit_or (eq v_4001 (expression.bv_nat 1 1)) (eq v_4003 (expression.bv_nat 1 1))) (expression.bv_nat 8 1) (expression.bv_nat 8 0));
      pure ()
    pat_end;
    pattern fun (v_2489 : Mem) => do
      v_9483 <- evaluateAddress v_2489;
      v_9484 <- getRegister cf;
      v_9486 <- getRegister zf;
      store v_9483 (mux (bit_or (eq v_9484 (expression.bv_nat 1 1)) (eq v_9486 (expression.bv_nat 1 1))) (expression.bv_nat 8 1) (expression.bv_nat 8 0)) 1;
      pure ()
    pat_end
