def cmovnpw1 : instruction :=
  definst "cmovnpw" $ do
    pattern fun (v_3031 : reg (bv 16)) (v_3032 : reg (bv 16)) => do
      v_4912 <- getRegister pf;
      v_4915 <- getRegister v_3031;
      v_4916 <- getRegister v_3032;
      setRegister (lhs.of_reg v_3032) (mux (notBool_ (eq v_4912 (expression.bv_nat 1 1))) v_4915 v_4916);
      pure ()
    pat_end;
    pattern fun (v_3028 : Mem) (v_3027 : reg (bv 16)) => do
      v_8455 <- getRegister pf;
      v_8458 <- evaluateAddress v_3028;
      v_8459 <- load v_8458 2;
      v_8460 <- getRegister v_3027;
      setRegister (lhs.of_reg v_3027) (mux (notBool_ (eq v_8455 (expression.bv_nat 1 1))) v_8459 v_8460);
      pure ()
    pat_end
