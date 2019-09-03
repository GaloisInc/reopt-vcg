def sete1 : instruction :=
  definst "sete" $ do
    pattern fun (v_2451 : reg (bv 8)) => do
      v_3917 <- getRegister zf;
      setRegister (lhs.of_reg v_2451) (mux (eq v_3917 (expression.bv_nat 1 1)) (expression.bv_nat 8 1) (expression.bv_nat 8 0));
      pure ()
    pat_end;
    pattern fun (v_2447 : Mem) => do
      v_9461 <- evaluateAddress v_2447;
      v_9462 <- getRegister zf;
      store v_9461 (mux (eq v_9462 (expression.bv_nat 1 1)) (expression.bv_nat 8 1) (expression.bv_nat 8 0)) 1;
      pure ()
    pat_end
