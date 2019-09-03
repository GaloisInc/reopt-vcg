def cmovnpl1 : instruction :=
  definst "cmovnpl" $ do
    pattern fun (v_3025 : reg (bv 32)) (v_3026 : reg (bv 32)) => do
      v_4903 <- getRegister pf;
      v_4906 <- getRegister v_3025;
      v_4907 <- getRegister v_3026;
      setRegister (lhs.of_reg v_3026) (mux (notBool_ (eq v_4903 (expression.bv_nat 1 1))) v_4906 v_4907);
      pure ()
    pat_end;
    pattern fun (v_3021 : Mem) (v_3022 : reg (bv 32)) => do
      v_8412 <- getRegister pf;
      v_8415 <- evaluateAddress v_3021;
      v_8416 <- load v_8415 4;
      v_8417 <- getRegister v_3022;
      setRegister (lhs.of_reg v_3022) (mux (notBool_ (eq v_8412 (expression.bv_nat 1 1))) v_8416 v_8417);
      pure ()
    pat_end
