def sets1 : instruction :=
  definst "sets" $ do
    pattern fun (v_2691 : reg (bv 8)) => do
      v_4273 <- getRegister sf;
      setRegister (lhs.of_reg v_2691) (mux (eq v_4273 (expression.bv_nat 1 1)) (expression.bv_nat 8 1) (expression.bv_nat 8 0));
      pure ()
    pat_end;
    pattern fun (v_2687 : Mem) => do
      v_9610 <- evaluateAddress v_2687;
      v_9611 <- getRegister sf;
      store v_9610 (mux (eq v_9611 (expression.bv_nat 1 1)) (expression.bv_nat 8 1) (expression.bv_nat 8 0)) 1;
      pure ()
    pat_end
