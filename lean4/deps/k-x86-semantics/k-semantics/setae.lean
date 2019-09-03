def setae1 : instruction :=
  definst "setae" $ do
    pattern fun (v_2394 : reg (bv 8)) => do
      v_3852 <- getRegister cf;
      setRegister (lhs.of_reg v_2394) (mux (notBool_ (eq v_3852 (expression.bv_nat 1 1))) (expression.bv_nat 8 1) (expression.bv_nat 8 0));
      pure ()
    pat_end;
    pattern fun (v_2390 : Mem) => do
      v_9413 <- evaluateAddress v_2390;
      v_9414 <- getRegister cf;
      store v_9413 (mux (notBool_ (eq v_9414 (expression.bv_nat 1 1))) (expression.bv_nat 8 1) (expression.bv_nat 8 0)) 1;
      pure ()
    pat_end
