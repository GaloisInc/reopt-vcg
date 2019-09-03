def setng1 : instruction :=
  definst "setng" $ do
    pattern fun (v_2572 : reg (bv 8)) => do
      v_4102 <- getRegister zf;
      v_4104 <- getRegister sf;
      v_4106 <- getRegister of;
      setRegister (lhs.of_reg v_2572) (mux (bit_or (eq v_4102 (expression.bv_nat 1 1)) (notBool_ (eq (eq v_4104 (expression.bv_nat 1 1)) (eq v_4106 (expression.bv_nat 1 1))))) (expression.bv_nat 8 1) (expression.bv_nat 8 0));
      pure ()
    pat_end;
    pattern fun (v_2568 : Mem) => do
      v_9548 <- evaluateAddress v_2568;
      v_9549 <- getRegister zf;
      v_9551 <- getRegister sf;
      v_9553 <- getRegister of;
      store v_9548 (mux (bit_or (eq v_9549 (expression.bv_nat 1 1)) (notBool_ (eq (eq v_9551 (expression.bv_nat 1 1)) (eq v_9553 (expression.bv_nat 1 1))))) (expression.bv_nat 8 1) (expression.bv_nat 8 0)) 1;
      pure ()
    pat_end
