def setna1 : instruction :=
  definst "setna" $ do
    pattern fun (v_2561 : reg (bv 8)) => do
      v_4072 <- getRegister cf;
      v_4074 <- getRegister zf;
      setRegister (lhs.of_reg v_2561) (mux (bit_or (eq v_4072 (expression.bv_nat 1 1)) (eq v_4074 (expression.bv_nat 1 1))) (expression.bv_nat 8 1) (expression.bv_nat 8 0));
      pure ()
    pat_end;
    pattern fun (v_2553 : Mem) => do
      v_8530 <- evaluateAddress v_2553;
      v_8531 <- getRegister cf;
      v_8533 <- getRegister zf;
      store v_8530 (mux (bit_or (eq v_8531 (expression.bv_nat 1 1)) (eq v_8533 (expression.bv_nat 1 1))) (expression.bv_nat 8 1) (expression.bv_nat 8 0)) 1;
      pure ()
    pat_end
