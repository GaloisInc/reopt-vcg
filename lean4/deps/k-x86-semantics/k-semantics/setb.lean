def setb1 : instruction :=
  definst "setb" $ do
    pattern fun (v_2500 : reg (bv 8)) => do
      v_3953 <- getRegister cf;
      setRegister (lhs.of_reg v_2500) (mux v_3953 (expression.bv_nat 8 1) (expression.bv_nat 8 0));
      pure ()
    pat_end;
    pattern fun (v_2493 : Mem) => do
      v_7902 <- evaluateAddress v_2493;
      v_7903 <- getRegister cf;
      store v_7902 (mux v_7903 (expression.bv_nat 8 1) (expression.bv_nat 8 0)) 1;
      pure ()
    pat_end
