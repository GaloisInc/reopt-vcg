def setp1 : instruction :=
  definst "setp" $ do
    pattern fun (v_2753 : reg (bv 8)) => do
      v_4250 <- getRegister pf;
      setRegister (lhs.of_reg v_2753) (mux v_4250 (expression.bv_nat 8 1) (expression.bv_nat 8 0));
      pure ()
    pat_end;
    pattern fun (v_2746 : Mem) => do
      v_8039 <- evaluateAddress v_2746;
      v_8040 <- getRegister pf;
      store v_8039 (mux v_8040 (expression.bv_nat 8 1) (expression.bv_nat 8 0)) 1;
      pure ()
    pat_end
