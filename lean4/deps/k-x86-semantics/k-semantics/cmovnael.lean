def cmovnael1 : instruction :=
  definst "cmovnael" $ do
    pattern fun (v_2728 : reg (bv 32)) (v_2729 : reg (bv 32)) => do
      v_4474 <- getRegister cf;
      v_4476 <- getRegister v_2728;
      v_4477 <- getRegister v_2729;
      setRegister (lhs.of_reg v_2729) (mux (eq v_4474 (expression.bv_nat 1 1)) v_4476 v_4477);
      pure ()
    pat_end;
    pattern fun (v_2724 : Mem) (v_2725 : reg (bv 32)) => do
      v_8082 <- getRegister cf;
      v_8084 <- evaluateAddress v_2724;
      v_8085 <- load v_8084 4;
      v_8086 <- getRegister v_2725;
      setRegister (lhs.of_reg v_2725) (mux (eq v_8082 (expression.bv_nat 1 1)) v_8085 v_8086);
      pure ()
    pat_end
