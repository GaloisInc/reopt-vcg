def cmovnpq1 : instruction :=
  definst "cmovnpq" $ do
    pattern fun (v_3023 : reg (bv 64)) (v_3024 : reg (bv 64)) => do
      v_4901 <- getRegister pf;
      v_4904 <- getRegister v_3023;
      v_4905 <- getRegister v_3024;
      setRegister (lhs.of_reg v_3024) (mux (notBool_ (eq v_4901 (expression.bv_nat 1 1))) v_4904 v_4905);
      pure ()
    pat_end;
    pattern fun (v_3018 : Mem) (v_3019 : reg (bv 64)) => do
      v_8447 <- getRegister pf;
      v_8450 <- evaluateAddress v_3018;
      v_8451 <- load v_8450 8;
      v_8452 <- getRegister v_3019;
      setRegister (lhs.of_reg v_3019) (mux (notBool_ (eq v_8447 (expression.bv_nat 1 1))) v_8451 v_8452);
      pure ()
    pat_end
