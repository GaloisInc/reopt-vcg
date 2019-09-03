def cmovnsw1 : instruction :=
  definst "cmovnsw" $ do
    pattern fun (v_3096 : reg (bv 16)) (v_3097 : reg (bv 16)) => do
      v_4973 <- getRegister sf;
      v_4976 <- getRegister v_3096;
      v_4977 <- getRegister v_3097;
      setRegister (lhs.of_reg v_3097) (mux (notBool_ (eq v_4973 (expression.bv_nat 1 1))) v_4976 v_4977);
      pure ()
    pat_end;
    pattern fun (v_3086 : Mem) (v_3088 : reg (bv 16)) => do
      v_8455 <- getRegister sf;
      v_8458 <- evaluateAddress v_3086;
      v_8459 <- load v_8458 2;
      v_8460 <- getRegister v_3088;
      setRegister (lhs.of_reg v_3088) (mux (notBool_ (eq v_8455 (expression.bv_nat 1 1))) v_8459 v_8460);
      pure ()
    pat_end
