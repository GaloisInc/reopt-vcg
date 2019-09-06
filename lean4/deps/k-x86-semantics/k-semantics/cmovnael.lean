def cmovnael1 : instruction :=
  definst "cmovnael" $ do
    pattern fun (v_2809 : reg (bv 32)) (v_2810 : reg (bv 32)) => do
      v_4499 <- getRegister cf;
      v_4500 <- getRegister v_2809;
      v_4501 <- getRegister v_2810;
      setRegister (lhs.of_reg v_2810) (mux v_4499 v_4500 v_4501);
      pure ()
    pat_end;
    pattern fun (v_2802 : Mem) (v_2805 : reg (bv 32)) => do
      v_7895 <- getRegister cf;
      v_7896 <- evaluateAddress v_2802;
      v_7897 <- load v_7896 4;
      v_7898 <- getRegister v_2805;
      setRegister (lhs.of_reg v_2805) (mux v_7895 v_7897 v_7898);
      pure ()
    pat_end
