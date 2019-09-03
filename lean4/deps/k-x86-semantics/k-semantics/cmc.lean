def cmc1 : instruction :=
  definst "cmc" $ do
    pattern fun => do
      v_6970 <- getRegister cf;
      setRegister cf (mux (eq v_6970 (expression.bv_nat 1 1)) (expression.bv_nat 1 0) (expression.bv_nat 1 1));
      pure ()
    pat_end
