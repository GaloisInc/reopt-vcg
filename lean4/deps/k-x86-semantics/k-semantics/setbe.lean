def setbe1 : instruction :=
  definst "setbe" $ do
    pattern fun (v_2429 : reg (bv 8)) => do
      v_3889 <- getRegister cf;
      v_3891 <- getRegister zf;
      setRegister (lhs.of_reg v_2429) (mux (bit_or (eq v_3889 (expression.bv_nat 1 1)) (eq v_3891 (expression.bv_nat 1 1))) (expression.bv_nat 8 1) (expression.bv_nat 8 0));
      pure ()
    pat_end;
    pattern fun (v_2425 : Mem) => do
      v_9448 <- evaluateAddress v_2425;
      v_9449 <- getRegister cf;
      v_9451 <- getRegister zf;
      store v_9448 (mux (bit_or (eq v_9449 (expression.bv_nat 1 1)) (eq v_9451 (expression.bv_nat 1 1))) (expression.bv_nat 8 1) (expression.bv_nat 8 0)) 1;
      pure ()
    pat_end
