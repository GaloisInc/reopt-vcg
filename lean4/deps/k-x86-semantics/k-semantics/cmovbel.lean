def cmovbel1 : instruction :=
  definst "cmovbel" $ do
    pattern fun (v_2448 : reg (bv 32)) (v_2449 : reg (bv 32)) => do
      v_4122 <- getRegister cf;
      v_4124 <- getRegister zf;
      v_4127 <- getRegister v_2448;
      v_4128 <- getRegister v_2449;
      setRegister (lhs.of_reg v_2449) (mux (bit_or (eq v_4122 (expression.bv_nat 1 1)) (eq v_4124 (expression.bv_nat 1 1))) v_4127 v_4128);
      pure ()
    pat_end;
    pattern fun (v_2440 : Mem) (v_2441 : reg (bv 32)) => do
      v_7834 <- getRegister cf;
      v_7836 <- getRegister zf;
      v_7839 <- evaluateAddress v_2440;
      v_7840 <- load v_7839 4;
      v_7841 <- getRegister v_2441;
      setRegister (lhs.of_reg v_2441) (mux (bit_or (eq v_7834 (expression.bv_nat 1 1)) (eq v_7836 (expression.bv_nat 1 1))) v_7840 v_7841);
      pure ()
    pat_end
