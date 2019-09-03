def cmovnbw1 : instruction :=
  definst "cmovnbw" $ do
    pattern fun (v_2815 : reg (bv 16)) (v_2816 : reg (bv 16)) => do
      v_4597 <- getRegister cf;
      v_4600 <- getRegister v_2815;
      v_4601 <- getRegister v_2816;
      setRegister (lhs.of_reg v_2816) (mux (notBool_ (eq v_4597 (expression.bv_nat 1 1))) v_4600 v_4601);
      pure ()
    pat_end;
    pattern fun (v_2812 : Mem) (v_2811 : reg (bv 16)) => do
      v_8212 <- getRegister cf;
      v_8215 <- evaluateAddress v_2812;
      v_8216 <- load v_8215 2;
      v_8217 <- getRegister v_2811;
      setRegister (lhs.of_reg v_2811) (mux (notBool_ (eq v_8212 (expression.bv_nat 1 1))) v_8216 v_8217);
      pure ()
    pat_end
