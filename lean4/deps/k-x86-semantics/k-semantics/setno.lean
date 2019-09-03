def setno1 : instruction :=
  definst "setno" $ do
    pattern fun (v_2616 : reg (bv 8)) => do
      v_4188 <- getRegister of;
      setRegister (lhs.of_reg v_2616) (mux (notBool_ (eq v_4188 (expression.bv_nat 1 1))) (expression.bv_nat 8 1) (expression.bv_nat 8 0));
      pure ()
    pat_end;
    pattern fun (v_2612 : Mem) => do
      v_9589 <- evaluateAddress v_2612;
      v_9590 <- getRegister of;
      store v_9589 (mux (notBool_ (eq v_9590 (expression.bv_nat 1 1))) (expression.bv_nat 8 1) (expression.bv_nat 8 0)) 1;
      pure ()
    pat_end
