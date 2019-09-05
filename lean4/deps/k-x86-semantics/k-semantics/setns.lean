def setns1 : instruction :=
  definst "setns" $ do
    pattern fun (v_2693 : reg (bv 8)) => do
      v_4270 <- getRegister sf;
      setRegister (lhs.of_reg v_2693) (mux (notBool_ (eq v_4270 (expression.bv_nat 1 1))) (expression.bv_nat 8 1) (expression.bv_nat 8 0));
      pure ()
    pat_end;
    pattern fun (v_2685 : Mem) => do
      v_8624 <- evaluateAddress v_2685;
      v_8625 <- getRegister sf;
      store v_8624 (mux (notBool_ (eq v_8625 (expression.bv_nat 1 1))) (expression.bv_nat 8 1) (expression.bv_nat 8 0)) 1;
      pure ()
    pat_end
