def cmc1 : instruction :=
  definst "cmc" $ do
    pattern fun => do
      v_0 <- getRegister cf;
      setRegister cf (notBool_ v_0);
      pure ()
    pat_end
