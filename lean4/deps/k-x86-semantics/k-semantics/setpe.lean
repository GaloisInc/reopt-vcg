def setpe1 : instruction :=
  definst "setpe" $ do
    pattern fun (v_2737 : reg (bv 8)) => do
      v_4317 <- getRegister pf;
      setRegister (lhs.of_reg v_2737) (mux (eq v_4317 (expression.bv_nat 1 1)) (expression.bv_nat 8 1) (expression.bv_nat 8 0));
      pure ()
    pat_end;
    pattern fun (v_2729 : Mem) => do
      v_8646 <- evaluateAddress v_2729;
      v_8647 <- getRegister pf;
      store v_8646 (mux (eq v_8647 (expression.bv_nat 1 1)) (expression.bv_nat 8 1) (expression.bv_nat 8 0)) 1;
      pure ()
    pat_end
