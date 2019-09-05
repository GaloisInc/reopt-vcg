def cmovnpq1 : instruction :=
  definst "cmovnpq" $ do
    pattern fun (v_3086 : reg (bv 64)) (v_3087 : reg (bv 64)) => do
      v_4965 <- getRegister pf;
      v_4968 <- getRegister v_3086;
      v_4969 <- getRegister v_3087;
      setRegister (lhs.of_reg v_3087) (mux (notBool_ (eq v_4965 (expression.bv_nat 1 1))) v_4968 v_4969);
      pure ()
    pat_end;
    pattern fun (v_3081 : Mem) (v_3082 : reg (bv 64)) => do
      v_8433 <- getRegister pf;
      v_8436 <- evaluateAddress v_3081;
      v_8437 <- load v_8436 8;
      v_8438 <- getRegister v_3082;
      setRegister (lhs.of_reg v_3082) (mux (notBool_ (eq v_8433 (expression.bv_nat 1 1))) v_8437 v_8438);
      pure ()
    pat_end
