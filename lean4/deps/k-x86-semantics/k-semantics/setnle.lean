def setnle1 : instruction :=
  definst "setnle" $ do
    pattern fun (v_2592 : reg (bv 8)) => do
      v_4150 <- getRegister zf;
      v_4153 <- getRegister sf;
      v_4155 <- getRegister of;
      setRegister (lhs.of_reg v_2592) (mux (bit_and (notBool_ (eq v_4150 (expression.bv_nat 1 1))) (eq (eq v_4153 (expression.bv_nat 1 1)) (eq v_4155 (expression.bv_nat 1 1)))) (expression.bv_nat 8 1) (expression.bv_nat 8 0));
      pure ()
    pat_end;
    pattern fun (v_2588 : Mem) => do
      v_9553 <- evaluateAddress v_2588;
      v_9554 <- getRegister zf;
      v_9557 <- getRegister sf;
      v_9559 <- getRegister of;
      store v_9553 (mux (bit_and (notBool_ (eq v_9554 (expression.bv_nat 1 1))) (eq (eq v_9557 (expression.bv_nat 1 1)) (eq v_9559 (expression.bv_nat 1 1)))) (expression.bv_nat 8 1) (expression.bv_nat 8 0)) 1;
      pure ()
    pat_end
