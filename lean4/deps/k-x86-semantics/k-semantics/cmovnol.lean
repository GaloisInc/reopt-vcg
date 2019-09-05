def cmovnol1 : instruction :=
  definst "cmovnol" $ do
    pattern fun (v_3052 : reg (bv 32)) (v_3053 : reg (bv 32)) => do
      v_4921 <- getRegister of;
      v_4924 <- getRegister v_3052;
      v_4925 <- getRegister v_3053;
      setRegister (lhs.of_reg v_3053) (mux (notBool_ (eq v_4921 (expression.bv_nat 1 1))) v_4924 v_4925);
      pure ()
    pat_end;
    pattern fun (v_3045 : Mem) (v_3048 : reg (bv 32)) => do
      v_8401 <- getRegister of;
      v_8404 <- evaluateAddress v_3045;
      v_8405 <- load v_8404 4;
      v_8406 <- getRegister v_3048;
      setRegister (lhs.of_reg v_3048) (mux (notBool_ (eq v_8401 (expression.bv_nat 1 1))) v_8405 v_8406);
      pure ()
    pat_end
