def setnc1 : instruction :=
  definst "setnc" $ do
    pattern fun (v_2537 : reg (bv 8)) => do
      v_4063 <- getRegister cf;
      setRegister (lhs.of_reg v_2537) (mux (notBool_ (eq v_4063 (expression.bv_nat 1 1))) (expression.bv_nat 8 1) (expression.bv_nat 8 0));
      pure ()
    pat_end;
    pattern fun (v_2533 : Mem) => do
      v_9512 <- evaluateAddress v_2533;
      v_9513 <- getRegister cf;
      store v_9512 (mux (notBool_ (eq v_9513 (expression.bv_nat 1 1))) (expression.bv_nat 8 1) (expression.bv_nat 8 0)) 1;
      pure ()
    pat_end
