def cmovzw1 : instruction :=
  definst "cmovzw" $ do
    pattern fun (v_3309 : reg (bv 16)) (v_3310 : reg (bv 16)) => do
      v_5205 <- getRegister zf;
      v_5207 <- getRegister v_3309;
      v_5208 <- getRegister v_3310;
      setRegister (lhs.of_reg v_3310) (mux (eq v_5205 (expression.bv_nat 1 1)) v_5207 v_5208);
      pure ()
    pat_end;
    pattern fun (v_3303 : Mem) (v_3305 : reg (bv 16)) => do
      v_8612 <- getRegister zf;
      v_8614 <- evaluateAddress v_3303;
      v_8615 <- load v_8614 2;
      v_8616 <- getRegister v_3305;
      setRegister (lhs.of_reg v_3305) (mux (eq v_8612 (expression.bv_nat 1 1)) v_8615 v_8616);
      pure ()
    pat_end
