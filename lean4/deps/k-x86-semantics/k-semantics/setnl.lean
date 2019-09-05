def setnl1 : instruction :=
  definst "setnl" $ do
    pattern fun (v_2649 : reg (bv 8)) => do
      v_4204 <- getRegister sf;
      v_4206 <- getRegister of;
      setRegister (lhs.of_reg v_2649) (mux (eq (eq v_4204 (expression.bv_nat 1 1)) (eq v_4206 (expression.bv_nat 1 1))) (expression.bv_nat 8 1) (expression.bv_nat 8 0));
      pure ()
    pat_end;
    pattern fun (v_2641 : Mem) => do
      v_8592 <- evaluateAddress v_2641;
      v_8593 <- getRegister sf;
      v_8595 <- getRegister of;
      store v_8592 (mux (eq (eq v_8593 (expression.bv_nat 1 1)) (eq v_8595 (expression.bv_nat 1 1))) (expression.bv_nat 8 1) (expression.bv_nat 8 0)) 1;
      pure ()
    pat_end
