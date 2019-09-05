def setge1 : instruction :=
  definst "setge" $ do
    pattern fun (v_2528 : reg (bv 8)) => do
      v_4011 <- getRegister sf;
      v_4013 <- getRegister of;
      setRegister (lhs.of_reg v_2528) (mux (eq (eq v_4011 (expression.bv_nat 1 1)) (eq v_4013 (expression.bv_nat 1 1))) (expression.bv_nat 8 1) (expression.bv_nat 8 0));
      pure ()
    pat_end;
    pattern fun (v_2520 : Mem) => do
      v_8501 <- evaluateAddress v_2520;
      v_8502 <- getRegister sf;
      v_8504 <- getRegister of;
      store v_8501 (mux (eq (eq v_8502 (expression.bv_nat 1 1)) (eq v_8504 (expression.bv_nat 1 1))) (expression.bv_nat 8 1) (expression.bv_nat 8 0)) 1;
      pure ()
    pat_end
