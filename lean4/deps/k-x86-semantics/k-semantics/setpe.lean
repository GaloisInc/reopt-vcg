def setpe1 : instruction :=
  definst "setpe" $ do
    pattern fun (v_2682 : reg (bv 8)) => do
      v_4262 <- getRegister pf;
      setRegister (lhs.of_reg v_2682) (mux (eq v_4262 (expression.bv_nat 1 1)) (expression.bv_nat 8 1) (expression.bv_nat 8 0));
      pure ()
    pat_end;
    pattern fun (v_2678 : Mem) => do
      v_9623 <- evaluateAddress v_2678;
      v_9624 <- getRegister pf;
      store v_9623 (mux (eq v_9624 (expression.bv_nat 1 1)) (expression.bv_nat 8 1) (expression.bv_nat 8 0)) 1;
      pure ()
    pat_end
