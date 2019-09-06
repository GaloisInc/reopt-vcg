def setbe1 : instruction :=
  definst "setbe" $ do
    pattern fun (v_2511 : reg (bv 8)) => do
      v_3964 <- getRegister cf;
      v_3965 <- getRegister zf;
      setRegister (lhs.of_reg v_2511) (mux (bit_or v_3964 v_3965) (expression.bv_nat 8 1) (expression.bv_nat 8 0));
      pure ()
    pat_end;
    pattern fun (v_2504 : Mem) => do
      v_7906 <- evaluateAddress v_2504;
      v_7907 <- getRegister cf;
      v_7908 <- getRegister zf;
      store v_7906 (mux (bit_or v_7907 v_7908) (expression.bv_nat 8 1) (expression.bv_nat 8 0)) 1;
      pure ()
    pat_end
