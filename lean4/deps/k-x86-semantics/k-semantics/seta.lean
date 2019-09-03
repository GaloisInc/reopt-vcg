def seta1 : instruction :=
  definst "seta" $ do
    pattern fun (v_2383 : reg (bv 8)) => do
      v_3831 <- getRegister cf;
      v_3834 <- getRegister zf;
      setRegister (lhs.of_reg v_2383) (mux (bit_and (notBool_ (eq v_3831 (expression.bv_nat 1 1))) (notBool_ (eq v_3834 (expression.bv_nat 1 1)))) (expression.bv_nat 8 1) (expression.bv_nat 8 0));
      pure ()
    pat_end;
    pattern fun (v_2379 : Mem) => do
      v_9403 <- evaluateAddress v_2379;
      v_9404 <- getRegister cf;
      v_9407 <- getRegister zf;
      store v_9403 (mux (bit_and (notBool_ (eq v_9404 (expression.bv_nat 1 1))) (notBool_ (eq v_9407 (expression.bv_nat 1 1)))) (expression.bv_nat 8 1) (expression.bv_nat 8 0)) 1;
      pure ()
    pat_end
