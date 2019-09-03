def setpo1 : instruction :=
  definst "setpo" $ do
    pattern fun (v_2693 : reg (bv 8)) => do
      v_4273 <- getRegister pf;
      setRegister (lhs.of_reg v_2693) (mux (notBool_ (eq v_4273 (expression.bv_nat 1 1))) (expression.bv_nat 8 1) (expression.bv_nat 8 0));
      pure ()
    pat_end;
    pattern fun (v_2689 : Mem) => do
      v_9628 <- evaluateAddress v_2689;
      v_9629 <- getRegister pf;
      store v_9628 (mux (notBool_ (eq v_9629 (expression.bv_nat 1 1))) (expression.bv_nat 8 1) (expression.bv_nat 8 0)) 1;
      pure ()
    pat_end
