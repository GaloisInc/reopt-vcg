def cmovgl1 : instruction :=
  definst "cmovgl" $ do
    pattern fun (v_2623 : reg (bv 32)) (v_2624 : reg (bv 32)) => do
      v_4315 <- getRegister zf;
      v_4318 <- getRegister sf;
      v_4320 <- getRegister of;
      v_4324 <- getRegister v_2623;
      v_4325 <- getRegister v_2624;
      setRegister (lhs.of_reg v_2624) (mux (bit_and (notBool_ (eq v_4315 (expression.bv_nat 1 1))) (eq (eq v_4318 (expression.bv_nat 1 1)) (eq v_4320 (expression.bv_nat 1 1)))) v_4324 v_4325);
      pure ()
    pat_end;
    pattern fun (v_2619 : Mem) (v_2620 : reg (bv 32)) => do
      v_7962 <- getRegister zf;
      v_7965 <- getRegister sf;
      v_7967 <- getRegister of;
      v_7971 <- evaluateAddress v_2619;
      v_7972 <- load v_7971 4;
      v_7973 <- getRegister v_2620;
      setRegister (lhs.of_reg v_2620) (mux (bit_and (notBool_ (eq v_7962 (expression.bv_nat 1 1))) (eq (eq v_7965 (expression.bv_nat 1 1)) (eq v_7967 (expression.bv_nat 1 1)))) v_7972 v_7973);
      pure ()
    pat_end
