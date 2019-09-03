def setns1 : instruction :=
  definst "setns" $ do
    pattern fun (v_2638 : reg (bv 8)) => do
      v_4214 <- getRegister sf;
      setRegister (lhs.of_reg v_2638) (mux (notBool_ (eq v_4214 (expression.bv_nat 1 1))) (expression.bv_nat 8 1) (expression.bv_nat 8 0));
      pure ()
    pat_end;
    pattern fun (v_2634 : Mem) => do
      v_9601 <- evaluateAddress v_2634;
      v_9602 <- getRegister sf;
      store v_9601 (mux (notBool_ (eq v_9602 (expression.bv_nat 1 1))) (expression.bv_nat 8 1) (expression.bv_nat 8 0)) 1;
      pure ()
    pat_end
