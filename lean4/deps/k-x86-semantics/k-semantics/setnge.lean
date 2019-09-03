def setnge1 : instruction :=
  definst "setnge" $ do
    pattern fun (v_2583 : reg (bv 8)) => do
      v_4127 <- getRegister sf;
      v_4129 <- getRegister of;
      setRegister (lhs.of_reg v_2583) (mux (notBool_ (eq (eq v_4127 (expression.bv_nat 1 1)) (eq v_4129 (expression.bv_nat 1 1)))) (expression.bv_nat 8 1) (expression.bv_nat 8 0));
      pure ()
    pat_end;
    pattern fun (v_2579 : Mem) => do
      v_9560 <- evaluateAddress v_2579;
      v_9561 <- getRegister sf;
      v_9563 <- getRegister of;
      store v_9560 (mux (notBool_ (eq (eq v_9561 (expression.bv_nat 1 1)) (eq v_9563 (expression.bv_nat 1 1)))) (expression.bv_nat 8 1) (expression.bv_nat 8 0)) 1;
      pure ()
    pat_end
