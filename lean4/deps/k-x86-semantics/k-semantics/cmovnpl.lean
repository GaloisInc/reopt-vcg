def cmovnpl1 : instruction :=
  definst "cmovnpl" $ do
    pattern fun (v_3013 : reg (bv 32)) (v_3014 : reg (bv 32)) => do
      v_4890 <- getRegister pf;
      v_4893 <- getRegister v_3013;
      v_4894 <- getRegister v_3014;
      setRegister (lhs.of_reg v_3014) (mux (notBool_ (eq v_4890 (expression.bv_nat 1 1))) v_4893 v_4894);
      pure ()
    pat_end;
    pattern fun (v_3009 : Mem) (v_3010 : reg (bv 32)) => do
      v_8439 <- getRegister pf;
      v_8442 <- evaluateAddress v_3009;
      v_8443 <- load v_8442 4;
      v_8444 <- getRegister v_3010;
      setRegister (lhs.of_reg v_3010) (mux (notBool_ (eq v_8439 (expression.bv_nat 1 1))) v_8443 v_8444);
      pure ()
    pat_end
