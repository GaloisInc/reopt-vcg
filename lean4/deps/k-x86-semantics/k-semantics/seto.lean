def seto1 : instruction :=
  definst "seto" $ do
    pattern fun (v_2647 : reg (bv 8)) => do
      v_4227 <- getRegister of;
      setRegister (lhs.of_reg v_2647) (mux (eq v_4227 (expression.bv_nat 1 1)) (expression.bv_nat 8 1) (expression.bv_nat 8 0));
      pure ()
    pat_end;
    pattern fun (v_2643 : Mem) => do
      v_9589 <- evaluateAddress v_2643;
      v_9590 <- getRegister of;
      store v_9589 (mux (eq v_9590 (expression.bv_nat 1 1)) (expression.bv_nat 8 1) (expression.bv_nat 8 0)) 1;
      pure ()
    pat_end
