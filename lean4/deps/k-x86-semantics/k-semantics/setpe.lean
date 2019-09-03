def setpe1 : instruction :=
  definst "setpe" $ do
    pattern fun (v_2669 : reg (bv 8)) => do
      v_4249 <- getRegister pf;
      setRegister (lhs.of_reg v_2669) (mux (eq v_4249 (expression.bv_nat 1 1)) (expression.bv_nat 8 1) (expression.bv_nat 8 0));
      pure ()
    pat_end;
    pattern fun (v_2665 : Mem) => do
      v_9599 <- evaluateAddress v_2665;
      v_9600 <- getRegister pf;
      store v_9599 (mux (eq v_9600 (expression.bv_nat 1 1)) (expression.bv_nat 8 1) (expression.bv_nat 8 0)) 1;
      pure ()
    pat_end
