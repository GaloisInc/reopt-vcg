def setz1 : instruction :=
  definst "setz" $ do
    pattern fun (v_2702 : reg (bv 8)) => do
      v_4284 <- getRegister zf;
      setRegister (lhs.of_reg v_2702) (mux (eq v_4284 (expression.bv_nat 1 1)) (expression.bv_nat 8 1) (expression.bv_nat 8 0));
      pure ()
    pat_end;
    pattern fun (v_2698 : Mem) => do
      v_9615 <- evaluateAddress v_2698;
      v_9616 <- getRegister zf;
      store v_9615 (mux (eq v_9616 (expression.bv_nat 1 1)) (expression.bv_nat 8 1) (expression.bv_nat 8 0)) 1;
      pure ()
    pat_end
