def cmovnsl1 : instruction :=
  definst "cmovnsl" $ do
    pattern fun (v_3114 : reg (bv 32)) (v_3115 : reg (bv 32)) => do
      v_4992 <- getRegister sf;
      v_4995 <- getRegister v_3114;
      v_4996 <- getRegister v_3115;
      setRegister (lhs.of_reg v_3115) (mux (notBool_ (eq v_4992 (expression.bv_nat 1 1))) v_4995 v_4996);
      pure ()
    pat_end;
    pattern fun (v_3103 : Mem) (v_3106 : reg (bv 32)) => do
      v_8450 <- getRegister sf;
      v_8453 <- evaluateAddress v_3103;
      v_8454 <- load v_8453 4;
      v_8455 <- getRegister v_3106;
      setRegister (lhs.of_reg v_3106) (mux (notBool_ (eq v_8450 (expression.bv_nat 1 1))) v_8454 v_8455);
      pure ()
    pat_end
