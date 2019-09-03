def setnc1 : instruction :=
  definst "setnc" $ do
    pattern fun (v_2550 : reg (bv 8)) => do
      v_4076 <- getRegister cf;
      setRegister (lhs.of_reg v_2550) (mux (notBool_ (eq v_4076 (expression.bv_nat 1 1))) (expression.bv_nat 8 1) (expression.bv_nat 8 0));
      pure ()
    pat_end;
    pattern fun (v_2546 : Mem) => do
      v_9536 <- evaluateAddress v_2546;
      v_9537 <- getRegister cf;
      store v_9536 (mux (notBool_ (eq v_9537 (expression.bv_nat 1 1))) (expression.bv_nat 8 1) (expression.bv_nat 8 0)) 1;
      pure ()
    pat_end
