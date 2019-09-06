def cmovnpq1 : instruction :=
  definst "cmovnpq" $ do
    pattern fun (v_3112 : reg (bv 64)) (v_3113 : reg (bv 64)) => do
      v_4881 <- getRegister pf;
      v_4883 <- getRegister v_3112;
      v_4884 <- getRegister v_3113;
      setRegister (lhs.of_reg v_3113) (mux (notBool_ v_4881) v_4883 v_4884);
      pure ()
    pat_end;
    pattern fun (v_3108 : Mem) (v_3109 : reg (bv 64)) => do
      v_8175 <- getRegister pf;
      v_8177 <- evaluateAddress v_3108;
      v_8178 <- load v_8177 8;
      v_8179 <- getRegister v_3109;
      setRegister (lhs.of_reg v_3109) (mux (notBool_ v_8175) v_8178 v_8179);
      pure ()
    pat_end
