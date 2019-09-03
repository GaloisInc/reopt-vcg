def cmovnlew1 : instruction :=
  definst "cmovnlew" $ do
    pattern fun (v_2964 : reg (bv 16)) (v_2965 : reg (bv 16)) => do
      v_4814 <- getRegister zf;
      v_4817 <- getRegister sf;
      v_4819 <- getRegister of;
      v_4823 <- getRegister v_2964;
      v_4824 <- getRegister v_2965;
      setRegister (lhs.of_reg v_2965) (mux (bit_and (notBool_ (eq v_4814 (expression.bv_nat 1 1))) (eq (eq v_4817 (expression.bv_nat 1 1)) (eq v_4819 (expression.bv_nat 1 1)))) v_4823 v_4824);
      pure ()
    pat_end;
    pattern fun (v_2958 : Mem) (v_2960 : reg (bv 16)) => do
      v_8344 <- getRegister zf;
      v_8347 <- getRegister sf;
      v_8349 <- getRegister of;
      v_8353 <- evaluateAddress v_2958;
      v_8354 <- load v_8353 2;
      v_8355 <- getRegister v_2960;
      setRegister (lhs.of_reg v_2960) (mux (bit_and (notBool_ (eq v_8344 (expression.bv_nat 1 1))) (eq (eq v_8347 (expression.bv_nat 1 1)) (eq v_8349 (expression.bv_nat 1 1)))) v_8354 v_8355);
      pure ()
    pat_end
