def setnae1 : instruction :=
  definst "setnae" $ do
    pattern fun (v_2599 : reg (bv 8)) => do
      v_4072 <- getRegister cf;
      setRegister (lhs.of_reg v_2599) (mux v_4072 (expression.bv_nat 8 1) (expression.bv_nat 8 0));
      pure ()
    pat_end;
    pattern fun (v_2592 : Mem) => do
      v_7957 <- evaluateAddress v_2592;
      v_7958 <- getRegister cf;
      store v_7957 (mux v_7958 (expression.bv_nat 8 1) (expression.bv_nat 8 0)) 1;
      pure ()
    pat_end
