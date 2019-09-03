def cmovcq1 : instruction :=
  definst "cmovcq" $ do
    pattern fun (v_2527 : reg (bv 64)) (v_2528 : reg (bv 64)) => do
      v_4211 <- getRegister cf;
      v_4213 <- getRegister v_2527;
      v_4214 <- getRegister v_2528;
      setRegister (lhs.of_reg v_2528) (mux (eq v_4211 (expression.bv_nat 1 1)) v_4213 v_4214);
      pure ()
    pat_end;
    pattern fun (v_2523 : Mem) (v_2524 : reg (bv 64)) => do
      v_7894 <- getRegister cf;
      v_7896 <- evaluateAddress v_2523;
      v_7897 <- load v_7896 8;
      v_7898 <- getRegister v_2524;
      setRegister (lhs.of_reg v_2524) (mux (eq v_7894 (expression.bv_nat 1 1)) v_7897 v_7898);
      pure ()
    pat_end
