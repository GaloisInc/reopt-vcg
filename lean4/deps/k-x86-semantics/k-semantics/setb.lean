def setb1 : instruction :=
  definst "setb" $ do
    pattern fun (v_2405 : reg (bv 8)) => do
      v_3865 <- getRegister cf;
      setRegister (lhs.of_reg v_2405) (mux (eq v_3865 (expression.bv_nat 1 1)) (expression.bv_nat 8 1) (expression.bv_nat 8 0));
      pure ()
    pat_end;
    pattern fun (v_2401 : Mem) => do
      v_9419 <- evaluateAddress v_2401;
      v_9420 <- getRegister cf;
      store v_9419 (mux (eq v_9420 (expression.bv_nat 1 1)) (expression.bv_nat 8 1) (expression.bv_nat 8 0)) 1;
      pure ()
    pat_end
