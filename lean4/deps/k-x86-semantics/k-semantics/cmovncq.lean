def cmovncq1 : instruction :=
  definst "cmovncq" $ do
    pattern fun (v_2923 : reg (bv 64)) (v_2924 : reg (bv 64)) => do
      v_4638 <- getRegister cf;
      v_4640 <- getRegister v_2923;
      v_4641 <- getRegister v_2924;
      setRegister (lhs.of_reg v_2924) (mux (notBool_ v_4638) v_4640 v_4641);
      pure ()
    pat_end;
    pattern fun (v_2919 : Mem) (v_2920 : reg (bv 64)) => do
      v_7995 <- getRegister cf;
      v_7997 <- evaluateAddress v_2919;
      v_7998 <- load v_7997 8;
      v_7999 <- getRegister v_2920;
      setRegister (lhs.of_reg v_2920) (mux (notBool_ v_7995) v_7998 v_7999);
      pure ()
    pat_end
