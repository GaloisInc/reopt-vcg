def cmovbw1 : instruction :=
  definst "cmovbw" $ do
    pattern fun (v_2561 : reg (bv 16)) (v_2562 : reg (bv 16)) => do
      v_4242 <- getRegister cf;
      v_4244 <- getRegister v_2561;
      v_4245 <- getRegister v_2562;
      setRegister (lhs.of_reg v_2562) (mux (eq v_4242 (expression.bv_nat 1 1)) v_4244 v_4245);
      pure ()
    pat_end;
    pattern fun (v_2556 : Mem) (v_2557 : reg (bv 16)) => do
      v_7893 <- getRegister cf;
      v_7895 <- evaluateAddress v_2556;
      v_7896 <- load v_7895 2;
      v_7897 <- getRegister v_2557;
      setRegister (lhs.of_reg v_2557) (mux (eq v_7893 (expression.bv_nat 1 1)) v_7896 v_7897);
      pure ()
    pat_end
