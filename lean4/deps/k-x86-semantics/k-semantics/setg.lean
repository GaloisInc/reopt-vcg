def setg1 : instruction :=
  definst "setg" $ do
    pattern fun (v_2517 : reg (bv 8)) => do
      v_3990 <- getRegister zf;
      v_3993 <- getRegister sf;
      v_3995 <- getRegister of;
      setRegister (lhs.of_reg v_2517) (mux (bit_and (notBool_ (eq v_3990 (expression.bv_nat 1 1))) (eq (eq v_3993 (expression.bv_nat 1 1)) (eq v_3995 (expression.bv_nat 1 1)))) (expression.bv_nat 8 1) (expression.bv_nat 8 0));
      pure ()
    pat_end;
    pattern fun (v_2509 : Mem) => do
      v_8489 <- evaluateAddress v_2509;
      v_8490 <- getRegister zf;
      v_8493 <- getRegister sf;
      v_8495 <- getRegister of;
      store v_8489 (mux (bit_and (notBool_ (eq v_8490 (expression.bv_nat 1 1))) (eq (eq v_8493 (expression.bv_nat 1 1)) (eq v_8495 (expression.bv_nat 1 1)))) (expression.bv_nat 8 1) (expression.bv_nat 8 0)) 1;
      pure ()
    pat_end
