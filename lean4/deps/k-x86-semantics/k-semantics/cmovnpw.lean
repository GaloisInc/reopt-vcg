def cmovnpw1 : instruction :=
  definst "cmovnpw" $ do
    pattern fun (v_3095 : reg (bv 16)) (v_3096 : reg (bv 16)) => do
      v_4976 <- getRegister pf;
      v_4979 <- getRegister v_3095;
      v_4980 <- getRegister v_3096;
      setRegister (lhs.of_reg v_3096) (mux (notBool_ (eq v_4976 (expression.bv_nat 1 1))) v_4979 v_4980);
      pure ()
    pat_end;
    pattern fun (v_3090 : Mem) (v_3091 : reg (bv 16)) => do
      v_8441 <- getRegister pf;
      v_8444 <- evaluateAddress v_3090;
      v_8445 <- load v_8444 2;
      v_8446 <- getRegister v_3091;
      setRegister (lhs.of_reg v_3091) (mux (notBool_ (eq v_8441 (expression.bv_nat 1 1))) v_8445 v_8446);
      pure ()
    pat_end
