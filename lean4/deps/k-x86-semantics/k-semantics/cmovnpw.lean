def cmovnpw1 : instruction :=
  definst "cmovnpw" $ do
    pattern fun (v_3045 : reg (bv 16)) (v_3046 : reg (bv 16)) => do
      v_4925 <- getRegister pf;
      v_4928 <- getRegister v_3045;
      v_4929 <- getRegister v_3046;
      setRegister (lhs.of_reg v_3046) (mux (notBool_ (eq v_4925 (expression.bv_nat 1 1))) v_4928 v_4929);
      pure ()
    pat_end;
    pattern fun (v_3039 : Mem) (v_3041 : reg (bv 16)) => do
      v_8428 <- getRegister pf;
      v_8431 <- evaluateAddress v_3039;
      v_8432 <- load v_8431 2;
      v_8433 <- getRegister v_3041;
      setRegister (lhs.of_reg v_3041) (mux (notBool_ (eq v_8428 (expression.bv_nat 1 1))) v_8432 v_8433);
      pure ()
    pat_end
