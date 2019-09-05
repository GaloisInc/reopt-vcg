def setp1 : instruction :=
  definst "setp" $ do
    pattern fun (v_2726 : reg (bv 8)) => do
      v_4306 <- getRegister pf;
      setRegister (lhs.of_reg v_2726) (mux (eq v_4306 (expression.bv_nat 1 1)) (expression.bv_nat 8 1) (expression.bv_nat 8 0));
      pure ()
    pat_end;
    pattern fun (v_2718 : Mem) => do
      v_8641 <- evaluateAddress v_2718;
      v_8642 <- getRegister pf;
      store v_8641 (mux (eq v_8642 (expression.bv_nat 1 1)) (expression.bv_nat 8 1) (expression.bv_nat 8 0)) 1;
      pure ()
    pat_end
