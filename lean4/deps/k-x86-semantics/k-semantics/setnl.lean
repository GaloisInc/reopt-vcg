def setnl1 : instruction :=
  definst "setnl" $ do
    pattern fun (v_2594 : reg (bv 8)) => do
      v_4146 <- getRegister sf;
      v_4148 <- getRegister of;
      setRegister (lhs.of_reg v_2594) (mux (eq (eq v_4146 (expression.bv_nat 1 1)) (eq v_4148 (expression.bv_nat 1 1))) (expression.bv_nat 8 1) (expression.bv_nat 8 0));
      pure ()
    pat_end;
    pattern fun (v_2590 : Mem) => do
      v_9569 <- evaluateAddress v_2590;
      v_9570 <- getRegister sf;
      v_9572 <- getRegister of;
      store v_9569 (mux (eq (eq v_9570 (expression.bv_nat 1 1)) (eq v_9572 (expression.bv_nat 1 1))) (expression.bv_nat 8 1) (expression.bv_nat 8 0)) 1;
      pure ()
    pat_end
