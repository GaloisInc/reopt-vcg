def setnl1 : instruction :=
  definst "setnl" $ do
    pattern fun (v_2581 : reg (bv 8)) => do
      v_4133 <- getRegister sf;
      v_4135 <- getRegister of;
      setRegister (lhs.of_reg v_2581) (mux (eq (eq v_4133 (expression.bv_nat 1 1)) (eq v_4135 (expression.bv_nat 1 1))) (expression.bv_nat 8 1) (expression.bv_nat 8 0));
      pure ()
    pat_end;
    pattern fun (v_2577 : Mem) => do
      v_9545 <- evaluateAddress v_2577;
      v_9546 <- getRegister sf;
      v_9548 <- getRegister of;
      store v_9545 (mux (eq (eq v_9546 (expression.bv_nat 1 1)) (eq v_9548 (expression.bv_nat 1 1))) (expression.bv_nat 8 1) (expression.bv_nat 8 0)) 1;
      pure ()
    pat_end
