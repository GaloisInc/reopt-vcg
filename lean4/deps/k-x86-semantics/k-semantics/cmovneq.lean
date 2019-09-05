def cmovneq1 : instruction :=
  definst "cmovneq" $ do
    pattern fun (v_2924 : reg (bv 64)) (v_2925 : reg (bv 64)) => do
      v_4716 <- getRegister zf;
      v_4719 <- getRegister v_2924;
      v_4720 <- getRegister v_2925;
      setRegister (lhs.of_reg v_2925) (mux (notBool_ (eq v_4716 (expression.bv_nat 1 1))) v_4719 v_4720);
      pure ()
    pat_end;
    pattern fun (v_2919 : Mem) (v_2920 : reg (bv 64)) => do
      v_8238 <- getRegister zf;
      v_8241 <- evaluateAddress v_2919;
      v_8242 <- load v_8241 8;
      v_8243 <- getRegister v_2920;
      setRegister (lhs.of_reg v_2920) (mux (notBool_ (eq v_8238 (expression.bv_nat 1 1))) v_8242 v_8243);
      pure ()
    pat_end
