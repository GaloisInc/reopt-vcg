def setl1 : instruction :=
  definst "setl" $ do
    pattern fun (v_2471 : reg (bv 8)) => do
      v_3957 <- getRegister sf;
      v_3959 <- getRegister of;
      setRegister (lhs.of_reg v_2471) (mux (notBool_ (eq (eq v_3957 (expression.bv_nat 1 1)) (eq v_3959 (expression.bv_nat 1 1)))) (expression.bv_nat 8 1) (expression.bv_nat 8 0));
      pure ()
    pat_end;
    pattern fun (v_2467 : Mem) => do
      v_9462 <- evaluateAddress v_2467;
      v_9463 <- getRegister sf;
      v_9465 <- getRegister of;
      store v_9462 (mux (notBool_ (eq (eq v_9463 (expression.bv_nat 1 1)) (eq v_9465 (expression.bv_nat 1 1)))) (expression.bv_nat 8 1) (expression.bv_nat 8 0)) 1;
      pure ()
    pat_end
