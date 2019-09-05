def setbe1 : instruction :=
  definst "setbe" $ do
    pattern fun (v_2484 : reg (bv 8)) => do
      v_3947 <- getRegister cf;
      v_3949 <- getRegister zf;
      setRegister (lhs.of_reg v_2484) (mux (bit_or (eq v_3947 (expression.bv_nat 1 1)) (eq v_3949 (expression.bv_nat 1 1))) (expression.bv_nat 8 1) (expression.bv_nat 8 0));
      pure ()
    pat_end;
    pattern fun (v_2476 : Mem) => do
      v_8471 <- evaluateAddress v_2476;
      v_8472 <- getRegister cf;
      v_8474 <- getRegister zf;
      store v_8471 (mux (bit_or (eq v_8472 (expression.bv_nat 1 1)) (eq v_8474 (expression.bv_nat 1 1))) (expression.bv_nat 8 1) (expression.bv_nat 8 0)) 1;
      pure ()
    pat_end
