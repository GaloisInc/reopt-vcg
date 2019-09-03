def setno1 : instruction :=
  definst "setno" $ do
    pattern fun (v_2603 : reg (bv 8)) => do
      v_4175 <- getRegister of;
      setRegister (lhs.of_reg v_2603) (mux (notBool_ (eq v_4175 (expression.bv_nat 1 1))) (expression.bv_nat 8 1) (expression.bv_nat 8 0));
      pure ()
    pat_end;
    pattern fun (v_2599 : Mem) => do
      v_9565 <- evaluateAddress v_2599;
      v_9566 <- getRegister of;
      store v_9565 (mux (notBool_ (eq v_9566 (expression.bv_nat 1 1))) (expression.bv_nat 8 1) (expression.bv_nat 8 0)) 1;
      pure ()
    pat_end
