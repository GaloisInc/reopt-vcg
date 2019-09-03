def seto1 : instruction :=
  definst "seto" $ do
    pattern fun (v_2660 : reg (bv 8)) => do
      v_4240 <- getRegister of;
      setRegister (lhs.of_reg v_2660) (mux (eq v_4240 (expression.bv_nat 1 1)) (expression.bv_nat 8 1) (expression.bv_nat 8 0));
      pure ()
    pat_end;
    pattern fun (v_2656 : Mem) => do
      v_9613 <- evaluateAddress v_2656;
      v_9614 <- getRegister of;
      store v_9613 (mux (eq v_9614 (expression.bv_nat 1 1)) (expression.bv_nat 8 1) (expression.bv_nat 8 0)) 1;
      pure ()
    pat_end
