def cmovneq1 : instruction :=
  definst "cmovneq" $ do
    pattern fun (v_2861 : reg (bv 64)) (v_2862 : reg (bv 64)) => do
      v_4652 <- getRegister zf;
      v_4655 <- getRegister v_2861;
      v_4656 <- getRegister v_2862;
      setRegister (lhs.of_reg v_2862) (mux (notBool_ (eq v_4652 (expression.bv_nat 1 1))) v_4655 v_4656);
      pure ()
    pat_end;
    pattern fun (v_2856 : Mem) (v_2857 : reg (bv 64)) => do
      v_8252 <- getRegister zf;
      v_8255 <- evaluateAddress v_2856;
      v_8256 <- load v_8255 8;
      v_8257 <- getRegister v_2857;
      setRegister (lhs.of_reg v_2857) (mux (notBool_ (eq v_8252 (expression.bv_nat 1 1))) v_8256 v_8257);
      pure ()
    pat_end
