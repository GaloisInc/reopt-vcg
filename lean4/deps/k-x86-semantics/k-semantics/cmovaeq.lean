def cmovaeq1 : instruction :=
  definst "cmovaeq" $ do
    pattern fun (v_2384 : reg (bv 64)) (v_2385 : reg (bv 64)) => do
      v_4037 <- getRegister cf;
      v_4040 <- getRegister v_2384;
      v_4041 <- getRegister v_2385;
      setRegister (lhs.of_reg v_2385) (mux (notBool_ (eq v_4037 (expression.bv_nat 1 1))) v_4040 v_4041);
      pure ()
    pat_end;
    pattern fun (v_2379 : Mem) (v_2380 : reg (bv 64)) => do
      v_7808 <- getRegister cf;
      v_7811 <- evaluateAddress v_2379;
      v_7812 <- load v_7811 8;
      v_7813 <- getRegister v_2380;
      setRegister (lhs.of_reg v_2380) (mux (notBool_ (eq v_7808 (expression.bv_nat 1 1))) v_7812 v_7813);
      pure ()
    pat_end
