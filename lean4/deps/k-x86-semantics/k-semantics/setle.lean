def setle1 : instruction :=
  definst "setle" $ do
    pattern fun (v_2482 : reg (bv 8)) => do
      v_3976 <- getRegister zf;
      v_3978 <- getRegister sf;
      v_3980 <- getRegister of;
      setRegister (lhs.of_reg v_2482) (mux (bit_or (eq v_3976 (expression.bv_nat 1 1)) (notBool_ (eq (eq v_3978 (expression.bv_nat 1 1)) (eq v_3980 (expression.bv_nat 1 1))))) (expression.bv_nat 8 1) (expression.bv_nat 8 0));
      pure ()
    pat_end;
    pattern fun (v_2478 : Mem) => do
      v_9471 <- evaluateAddress v_2478;
      v_9472 <- getRegister zf;
      v_9474 <- getRegister sf;
      v_9476 <- getRegister of;
      store v_9471 (mux (bit_or (eq v_9472 (expression.bv_nat 1 1)) (notBool_ (eq (eq v_9474 (expression.bv_nat 1 1)) (eq v_9476 (expression.bv_nat 1 1))))) (expression.bv_nat 8 1) (expression.bv_nat 8 0)) 1;
      pure ()
    pat_end
