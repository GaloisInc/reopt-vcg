def setnae1 : instruction :=
  definst "setnae" $ do
    pattern fun (v_2517 : reg (bv 8)) => do
      v_4031 <- getRegister cf;
      setRegister (lhs.of_reg v_2517) (mux (eq v_4031 (expression.bv_nat 1 1)) (expression.bv_nat 8 1) (expression.bv_nat 8 0));
      pure ()
    pat_end;
    pattern fun (v_2513 : Mem) => do
      v_9515 <- evaluateAddress v_2513;
      v_9516 <- getRegister cf;
      store v_9515 (mux (eq v_9516 (expression.bv_nat 1 1)) (expression.bv_nat 8 1) (expression.bv_nat 8 0)) 1;
      pure ()
    pat_end
