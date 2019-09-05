def setnge1 : instruction :=
  definst "setnge" $ do
    pattern fun (v_2638 : reg (bv 8)) => do
      v_4186 <- getRegister sf;
      v_4188 <- getRegister of;
      setRegister (lhs.of_reg v_2638) (mux (notBool_ (eq (eq v_4186 (expression.bv_nat 1 1)) (eq v_4188 (expression.bv_nat 1 1)))) (expression.bv_nat 8 1) (expression.bv_nat 8 0));
      pure ()
    pat_end;
    pattern fun (v_2630 : Mem) => do
      v_8583 <- evaluateAddress v_2630;
      v_8584 <- getRegister sf;
      v_8586 <- getRegister of;
      store v_8583 (mux (notBool_ (eq (eq v_8584 (expression.bv_nat 1 1)) (eq v_8586 (expression.bv_nat 1 1)))) (expression.bv_nat 8 1) (expression.bv_nat 8 0)) 1;
      pure ()
    pat_end
