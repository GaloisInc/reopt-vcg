def seta1 : instruction :=
  definst "seta" $ do
    pattern fun (v_2396 : reg (bv 8)) => do
      v_3844 <- getRegister cf;
      v_3847 <- getRegister zf;
      setRegister (lhs.of_reg v_2396) (mux (bit_and (notBool_ (eq v_3844 (expression.bv_nat 1 1))) (notBool_ (eq v_3847 (expression.bv_nat 1 1)))) (expression.bv_nat 8 1) (expression.bv_nat 8 0));
      pure ()
    pat_end;
    pattern fun (v_2392 : Mem) => do
      v_9427 <- evaluateAddress v_2392;
      v_9428 <- getRegister cf;
      v_9431 <- getRegister zf;
      store v_9427 (mux (bit_and (notBool_ (eq v_9428 (expression.bv_nat 1 1))) (notBool_ (eq v_9431 (expression.bv_nat 1 1)))) (expression.bv_nat 8 1) (expression.bv_nat 8 0)) 1;
      pure ()
    pat_end
