def setae1 : instruction :=
  definst "setae" $ do
    pattern fun (v_2407 : reg (bv 8)) => do
      v_3865 <- getRegister cf;
      setRegister (lhs.of_reg v_2407) (mux (notBool_ (eq v_3865 (expression.bv_nat 1 1))) (expression.bv_nat 8 1) (expression.bv_nat 8 0));
      pure ()
    pat_end;
    pattern fun (v_2403 : Mem) => do
      v_9437 <- evaluateAddress v_2403;
      v_9438 <- getRegister cf;
      store v_9437 (mux (notBool_ (eq v_9438 (expression.bv_nat 1 1))) (expression.bv_nat 8 1) (expression.bv_nat 8 0)) 1;
      pure ()
    pat_end
