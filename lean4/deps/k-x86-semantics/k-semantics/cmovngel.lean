def cmovngel1 : instruction :=
  definst "cmovngel" $ do
    pattern fun (v_2944 : reg (bv 32)) (v_2945 : reg (bv 32)) => do
      v_4738 <- getRegister sf;
      v_4740 <- getRegister of;
      v_4744 <- getRegister v_2944;
      v_4745 <- getRegister v_2945;
      setRegister (lhs.of_reg v_2945) (mux (notBool_ (eq (eq v_4738 (expression.bv_nat 1 1)) (eq v_4740 (expression.bv_nat 1 1)))) v_4744 v_4745);
      pure ()
    pat_end;
    pattern fun (v_2937 : Mem) (v_2940 : reg (bv 32)) => do
      v_8254 <- getRegister sf;
      v_8256 <- getRegister of;
      v_8260 <- evaluateAddress v_2937;
      v_8261 <- load v_8260 4;
      v_8262 <- getRegister v_2940;
      setRegister (lhs.of_reg v_2940) (mux (notBool_ (eq (eq v_8254 (expression.bv_nat 1 1)) (eq v_8256 (expression.bv_nat 1 1)))) v_8261 v_8262);
      pure ()
    pat_end
