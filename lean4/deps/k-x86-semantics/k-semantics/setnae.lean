def setnae1 : instruction :=
  definst "setnae" $ do
    pattern fun (v_2504 : reg (bv 8)) => do
      v_4018 <- getRegister cf;
      setRegister (lhs.of_reg v_2504) (mux (eq v_4018 (expression.bv_nat 1 1)) (expression.bv_nat 8 1) (expression.bv_nat 8 0));
      pure ()
    pat_end;
    pattern fun (v_2500 : Mem) => do
      v_9491 <- evaluateAddress v_2500;
      v_9492 <- getRegister cf;
      store v_9491 (mux (eq v_9492 (expression.bv_nat 1 1)) (expression.bv_nat 8 1) (expression.bv_nat 8 0)) 1;
      pure ()
    pat_end
