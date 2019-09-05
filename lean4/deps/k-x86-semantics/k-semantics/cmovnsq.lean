def cmovnsq1 : instruction :=
  definst "cmovnsq" $ do
    pattern fun (v_3129 : reg (bv 64)) (v_3130 : reg (bv 64)) => do
      v_5008 <- getRegister sf;
      v_5011 <- getRegister v_3129;
      v_5012 <- getRegister v_3130;
      setRegister (lhs.of_reg v_3130) (mux (notBool_ (eq v_5008 (expression.bv_nat 1 1))) v_5011 v_5012);
      pure ()
    pat_end;
    pattern fun (v_3120 : Mem) (v_3121 : reg (bv 64)) => do
      v_8459 <- getRegister sf;
      v_8462 <- evaluateAddress v_3120;
      v_8463 <- load v_8462 8;
      v_8464 <- getRegister v_3121;
      setRegister (lhs.of_reg v_3121) (mux (notBool_ (eq v_8459 (expression.bv_nat 1 1))) v_8463 v_8464);
      pure ()
    pat_end
