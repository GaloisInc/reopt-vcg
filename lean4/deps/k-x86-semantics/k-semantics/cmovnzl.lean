def cmovnzl1 : instruction :=
  definst "cmovnzl" $ do
    pattern fun (v_3091 : reg (bv 32)) (v_3092 : reg (bv 32)) => do
      v_4971 <- getRegister zf;
      v_4974 <- getRegister v_3091;
      v_4975 <- getRegister v_3092;
      setRegister (lhs.of_reg v_3092) (mux (notBool_ (eq v_4971 (expression.bv_nat 1 1))) v_4974 v_4975);
      pure ()
    pat_end;
    pattern fun (v_3087 : Mem) (v_3088 : reg (bv 32)) => do
      v_8490 <- getRegister zf;
      v_8493 <- evaluateAddress v_3087;
      v_8494 <- load v_8493 4;
      v_8495 <- getRegister v_3088;
      setRegister (lhs.of_reg v_3088) (mux (notBool_ (eq v_8490 (expression.bv_nat 1 1))) v_8494 v_8495);
      pure ()
    pat_end
