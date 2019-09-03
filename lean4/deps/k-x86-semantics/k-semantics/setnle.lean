def setnle1 : instruction :=
  definst "setnle" $ do
    pattern fun (v_2605 : reg (bv 8)) => do
      v_4163 <- getRegister zf;
      v_4166 <- getRegister sf;
      v_4168 <- getRegister of;
      setRegister (lhs.of_reg v_2605) (mux (bit_and (notBool_ (eq v_4163 (expression.bv_nat 1 1))) (eq (eq v_4166 (expression.bv_nat 1 1)) (eq v_4168 (expression.bv_nat 1 1)))) (expression.bv_nat 8 1) (expression.bv_nat 8 0));
      pure ()
    pat_end;
    pattern fun (v_2601 : Mem) => do
      v_9577 <- evaluateAddress v_2601;
      v_9578 <- getRegister zf;
      v_9581 <- getRegister sf;
      v_9583 <- getRegister of;
      store v_9577 (mux (bit_and (notBool_ (eq v_9578 (expression.bv_nat 1 1))) (eq (eq v_9581 (expression.bv_nat 1 1)) (eq v_9583 (expression.bv_nat 1 1)))) (expression.bv_nat 8 1) (expression.bv_nat 8 0)) 1;
      pure ()
    pat_end
