def setns1 : instruction :=
  definst "setns" $ do
    pattern fun (v_2720 : reg (bv 8)) => do
      v_4220 <- getRegister sf;
      setRegister (lhs.of_reg v_2720) (mux (notBool_ v_4220) (expression.bv_nat 8 1) (expression.bv_nat 8 0));
      pure ()
    pat_end;
    pattern fun (v_2713 : Mem) => do
      v_8025 <- evaluateAddress v_2713;
      v_8026 <- getRegister sf;
      store v_8025 (mux (notBool_ v_8026) (expression.bv_nat 8 1) (expression.bv_nat 8 0)) 1;
      pure ()
    pat_end
