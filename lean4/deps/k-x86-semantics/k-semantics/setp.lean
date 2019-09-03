def setp1 : instruction :=
  definst "setp" $ do
    pattern fun (v_2658 : reg (bv 8)) => do
      v_4238 <- getRegister pf;
      setRegister (lhs.of_reg v_2658) (mux (eq v_4238 (expression.bv_nat 1 1)) (expression.bv_nat 8 1) (expression.bv_nat 8 0));
      pure ()
    pat_end;
    pattern fun (v_2654 : Mem) => do
      v_9594 <- evaluateAddress v_2654;
      v_9595 <- getRegister pf;
      store v_9594 (mux (eq v_9595 (expression.bv_nat 1 1)) (expression.bv_nat 8 1) (expression.bv_nat 8 0)) 1;
      pure ()
    pat_end
