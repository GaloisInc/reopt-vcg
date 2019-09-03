def cmovael1 : instruction :=
  definst "cmovael" $ do
    pattern fun (v_3286 : reg (bv 32)) (v_3287 : reg (bv 32)) => do
      v_7118 <- getRegister cf;
      v_7121 <- getRegister v_3286;
      v_7122 <- getRegister v_3287;
      setRegister (lhs.of_reg v_3287) (mux (notBool_ (eq v_7118 (expression.bv_nat 1 1))) v_7121 v_7122);
      pure ()
    pat_end;
    pattern fun (v_3281 : Mem) (v_3282 : reg (bv 32)) => do
      v_10517 <- getRegister cf;
      v_10520 <- evaluateAddress v_3281;
      v_10521 <- load v_10520 4;
      v_10522 <- getRegister v_3282;
      setRegister (lhs.of_reg v_3282) (mux (notBool_ (eq v_10517 (expression.bv_nat 1 1))) v_10521 v_10522);
      pure ()
    pat_end
