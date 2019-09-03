def setne1 : instruction :=
  definst "setne" $ do
    pattern fun (v_2548 : reg (bv 8)) => do
      v_4076 <- getRegister zf;
      setRegister (lhs.of_reg v_2548) (mux (notBool_ (eq v_4076 (expression.bv_nat 1 1))) (expression.bv_nat 8 1) (expression.bv_nat 8 0));
      pure ()
    pat_end;
    pattern fun (v_2544 : Mem) => do
      v_9518 <- evaluateAddress v_2544;
      v_9519 <- getRegister zf;
      store v_9518 (mux (notBool_ (eq v_9519 (expression.bv_nat 1 1))) (expression.bv_nat 8 1) (expression.bv_nat 8 0)) 1;
      pure ()
    pat_end
