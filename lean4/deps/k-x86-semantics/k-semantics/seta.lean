def seta1 : instruction :=
  definst "seta" $ do
    pattern fun (v_2451 : reg (bv 8)) => do
      v_3904 <- getRegister cf;
      v_3907 <- getRegister zf;
      setRegister (lhs.of_reg v_2451) (mux (bit_and (notBool_ (eq v_3904 (expression.bv_nat 1 1))) (notBool_ (eq v_3907 (expression.bv_nat 1 1)))) (expression.bv_nat 8 1) (expression.bv_nat 8 0));
      pure ()
    pat_end;
    pattern fun (v_2443 : Mem) => do
      v_8450 <- evaluateAddress v_2443;
      v_8451 <- getRegister cf;
      v_8454 <- getRegister zf;
      store v_8450 (mux (bit_and (notBool_ (eq v_8451 (expression.bv_nat 1 1))) (notBool_ (eq v_8454 (expression.bv_nat 1 1)))) (expression.bv_nat 8 1) (expression.bv_nat 8 0)) 1;
      pure ()
    pat_end
