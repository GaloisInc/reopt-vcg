def setng1 : instruction :=
  definst "setng" $ do
    pattern fun (v_2559 : reg (bv 8)) => do
      v_4089 <- getRegister zf;
      v_4091 <- getRegister sf;
      v_4093 <- getRegister of;
      setRegister (lhs.of_reg v_2559) (mux (bit_or (eq v_4089 (expression.bv_nat 1 1)) (notBool_ (eq (eq v_4091 (expression.bv_nat 1 1)) (eq v_4093 (expression.bv_nat 1 1))))) (expression.bv_nat 8 1) (expression.bv_nat 8 0));
      pure ()
    pat_end;
    pattern fun (v_2555 : Mem) => do
      v_9524 <- evaluateAddress v_2555;
      v_9525 <- getRegister zf;
      v_9527 <- getRegister sf;
      v_9529 <- getRegister of;
      store v_9524 (mux (bit_or (eq v_9525 (expression.bv_nat 1 1)) (notBool_ (eq (eq v_9527 (expression.bv_nat 1 1)) (eq v_9529 (expression.bv_nat 1 1))))) (expression.bv_nat 8 1) (expression.bv_nat 8 0)) 1;
      pure ()
    pat_end
