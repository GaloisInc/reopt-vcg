def cmovael1 : instruction :=
  definst "cmovael" $ do
    pattern fun (v_3273 : reg (bv 32)) (v_3274 : reg (bv 32)) => do
      v_6978 <- getRegister cf;
      v_6981 <- getRegister v_3273;
      v_6982 <- getRegister v_3274;
      setRegister (lhs.of_reg v_3274) (mux (notBool_ (eq v_6978 (expression.bv_nat 1 1))) v_6981 v_6982);
      pure ()
    pat_end;
    pattern fun (v_3268 : Mem) (v_3269 : reg (bv 32)) => do
      v_10231 <- getRegister cf;
      v_10234 <- evaluateAddress v_3268;
      v_10235 <- load v_10234 4;
      v_10236 <- getRegister v_3269;
      setRegister (lhs.of_reg v_3269) (mux (notBool_ (eq v_10231 (expression.bv_nat 1 1))) v_10235 v_10236);
      pure ()
    pat_end
