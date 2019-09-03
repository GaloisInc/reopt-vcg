def setge1 : instruction :=
  definst "setge" $ do
    pattern fun (v_2460 : reg (bv 8)) => do
      v_3940 <- getRegister sf;
      v_3942 <- getRegister of;
      setRegister (lhs.of_reg v_2460) (mux (eq (eq v_3940 (expression.bv_nat 1 1)) (eq v_3942 (expression.bv_nat 1 1))) (expression.bv_nat 8 1) (expression.bv_nat 8 0));
      pure ()
    pat_end;
    pattern fun (v_2456 : Mem) => do
      v_9454 <- evaluateAddress v_2456;
      v_9455 <- getRegister sf;
      v_9457 <- getRegister of;
      store v_9454 (mux (eq (eq v_9455 (expression.bv_nat 1 1)) (eq v_9457 (expression.bv_nat 1 1))) (expression.bv_nat 8 1) (expression.bv_nat 8 0)) 1;
      pure ()
    pat_end
