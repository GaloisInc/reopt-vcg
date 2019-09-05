def cmc1 : instruction :=
  definst "cmc" $ do
    pattern fun => do
      v_6809 <- getRegister cf;
      setRegister cf (notBool_ (eq v_6809 (expression.bv_nat 1 1)));
      pure ()
    pat_end
