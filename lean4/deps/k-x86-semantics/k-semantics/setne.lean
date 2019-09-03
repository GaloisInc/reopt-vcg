def setne1 : instruction :=
  definst "setne" $ do
    pattern fun (v_2561 : reg (bv 8)) => do
      v_4089 <- getRegister zf;
      setRegister (lhs.of_reg v_2561) (mux (notBool_ (eq v_4089 (expression.bv_nat 1 1))) (expression.bv_nat 8 1) (expression.bv_nat 8 0));
      pure ()
    pat_end;
    pattern fun (v_2557 : Mem) => do
      v_9542 <- evaluateAddress v_2557;
      v_9543 <- getRegister zf;
      store v_9542 (mux (notBool_ (eq v_9543 (expression.bv_nat 1 1))) (expression.bv_nat 8 1) (expression.bv_nat 8 0)) 1;
      pure ()
    pat_end
