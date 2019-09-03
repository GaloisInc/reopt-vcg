def cmovncq1 : instruction :=
  definst "cmovncq" $ do
    pattern fun (v_2834 : reg (bv 64)) (v_2835 : reg (bv 64)) => do
      v_4619 <- getRegister cf;
      v_4622 <- getRegister v_2834;
      v_4623 <- getRegister v_2835;
      setRegister (lhs.of_reg v_2835) (mux (notBool_ (eq v_4619 (expression.bv_nat 1 1))) v_4622 v_4623);
      pure ()
    pat_end;
    pattern fun (v_2829 : Mem) (v_2830 : reg (bv 64)) => do
      v_8228 <- getRegister cf;
      v_8231 <- evaluateAddress v_2829;
      v_8232 <- load v_8231 8;
      v_8233 <- getRegister v_2830;
      setRegister (lhs.of_reg v_2830) (mux (notBool_ (eq v_8228 (expression.bv_nat 1 1))) v_8232 v_8233);
      pure ()
    pat_end
