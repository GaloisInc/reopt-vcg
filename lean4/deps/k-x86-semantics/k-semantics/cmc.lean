def cmc1 : instruction :=
  definst "cmc" $ do
    pattern fun => do
      v_7110 <- getRegister cf;
      setRegister cf (mux (eq v_7110 (expression.bv_nat 1 1)) (expression.bv_nat 1 0) (expression.bv_nat 1 1));
      pure ()
    pat_end
