def setg1 : instruction :=
  definst "setg" $ do
    pattern fun (v_2462 : reg (bv 8)) => do
      v_3928 <- getRegister zf;
      v_3931 <- getRegister sf;
      v_3933 <- getRegister of;
      setRegister (lhs.of_reg v_2462) (mux (bit_and (notBool_ (eq v_3928 (expression.bv_nat 1 1))) (eq (eq v_3931 (expression.bv_nat 1 1)) (eq v_3933 (expression.bv_nat 1 1)))) (expression.bv_nat 8 1) (expression.bv_nat 8 0));
      pure ()
    pat_end;
    pattern fun (v_2458 : Mem) => do
      v_9466 <- evaluateAddress v_2458;
      v_9467 <- getRegister zf;
      v_9470 <- getRegister sf;
      v_9472 <- getRegister of;
      store v_9466 (mux (bit_and (notBool_ (eq v_9467 (expression.bv_nat 1 1))) (eq (eq v_9470 (expression.bv_nat 1 1)) (eq v_9472 (expression.bv_nat 1 1)))) (expression.bv_nat 8 1) (expression.bv_nat 8 0)) 1;
      pure ()
    pat_end
