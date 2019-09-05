def setle1 : instruction :=
  definst "setle" $ do
    pattern fun (v_2550 : reg (bv 8)) => do
      v_4051 <- getRegister zf;
      v_4053 <- getRegister sf;
      v_4055 <- getRegister of;
      setRegister (lhs.of_reg v_2550) (mux (bit_or (eq v_4051 (expression.bv_nat 1 1)) (notBool_ (eq (eq v_4053 (expression.bv_nat 1 1)) (eq v_4055 (expression.bv_nat 1 1))))) (expression.bv_nat 8 1) (expression.bv_nat 8 0));
      pure ()
    pat_end;
    pattern fun (v_2542 : Mem) => do
      v_8518 <- evaluateAddress v_2542;
      v_8519 <- getRegister zf;
      v_8521 <- getRegister sf;
      v_8523 <- getRegister of;
      store v_8518 (mux (bit_or (eq v_8519 (expression.bv_nat 1 1)) (notBool_ (eq (eq v_8521 (expression.bv_nat 1 1)) (eq v_8523 (expression.bv_nat 1 1))))) (expression.bv_nat 8 1) (expression.bv_nat 8 0)) 1;
      pure ()
    pat_end
