def sets1 : instruction :=
  definst "sets" $ do
    pattern fun (v_2704 : reg (bv 8)) => do
      v_4286 <- getRegister sf;
      setRegister (lhs.of_reg v_2704) (mux (eq v_4286 (expression.bv_nat 1 1)) (expression.bv_nat 8 1) (expression.bv_nat 8 0));
      pure ()
    pat_end;
    pattern fun (v_2700 : Mem) => do
      v_9634 <- evaluateAddress v_2700;
      v_9635 <- getRegister sf;
      store v_9634 (mux (eq v_9635 (expression.bv_nat 1 1)) (expression.bv_nat 8 1) (expression.bv_nat 8 0)) 1;
      pure ()
    pat_end
