def cmovnsq1 : instruction :=
  definst "cmovnsq" $ do
    pattern fun (v_3077 : reg (bv 64)) (v_3078 : reg (bv 64)) => do
      v_4957 <- getRegister sf;
      v_4960 <- getRegister v_3077;
      v_4961 <- getRegister v_3078;
      setRegister (lhs.of_reg v_3078) (mux (notBool_ (eq v_4957 (expression.bv_nat 1 1))) v_4960 v_4961);
      pure ()
    pat_end;
    pattern fun (v_3069 : Mem) (v_3070 : reg (bv 64)) => do
      v_8446 <- getRegister sf;
      v_8449 <- evaluateAddress v_3069;
      v_8450 <- load v_8449 8;
      v_8451 <- getRegister v_3070;
      setRegister (lhs.of_reg v_3070) (mux (notBool_ (eq v_8446 (expression.bv_nat 1 1))) v_8450 v_8451);
      pure ()
    pat_end
