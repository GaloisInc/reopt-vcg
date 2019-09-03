def setb1 : instruction :=
  definst "setb" $ do
    pattern fun (v_2418 : reg (bv 8)) => do
      v_3878 <- getRegister cf;
      setRegister (lhs.of_reg v_2418) (mux (eq v_3878 (expression.bv_nat 1 1)) (expression.bv_nat 8 1) (expression.bv_nat 8 0));
      pure ()
    pat_end;
    pattern fun (v_2414 : Mem) => do
      v_9443 <- evaluateAddress v_2414;
      v_9444 <- getRegister cf;
      store v_9443 (mux (eq v_9444 (expression.bv_nat 1 1)) (expression.bv_nat 8 1) (expression.bv_nat 8 0)) 1;
      pure ()
    pat_end
