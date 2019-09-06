def setpo1 : instruction :=
  definst "setpo" $ do
    pattern fun (v_2775 : reg (bv 8)) => do
      v_4269 <- getRegister pf;
      setRegister (lhs.of_reg v_2775) (mux (notBool_ v_4269) (expression.bv_nat 8 1) (expression.bv_nat 8 0));
      pure ()
    pat_end;
    pattern fun (v_2768 : Mem) => do
      v_8047 <- evaluateAddress v_2768;
      v_8048 <- getRegister pf;
      store v_8047 (mux (notBool_ v_8048) (expression.bv_nat 8 1) (expression.bv_nat 8 0)) 1;
      pure ()
    pat_end
