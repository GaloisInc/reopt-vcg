def setge1 : instruction :=
  definst "setge" $ do
    pattern fun (v_2473 : reg (bv 8)) => do
      v_3953 <- getRegister sf;
      v_3955 <- getRegister of;
      setRegister (lhs.of_reg v_2473) (mux (eq (eq v_3953 (expression.bv_nat 1 1)) (eq v_3955 (expression.bv_nat 1 1))) (expression.bv_nat 8 1) (expression.bv_nat 8 0));
      pure ()
    pat_end;
    pattern fun (v_2469 : Mem) => do
      v_9478 <- evaluateAddress v_2469;
      v_9479 <- getRegister sf;
      v_9481 <- getRegister of;
      store v_9478 (mux (eq (eq v_9479 (expression.bv_nat 1 1)) (eq v_9481 (expression.bv_nat 1 1))) (expression.bv_nat 8 1) (expression.bv_nat 8 0)) 1;
      pure ()
    pat_end
