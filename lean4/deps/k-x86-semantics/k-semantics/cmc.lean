def cmc1 : instruction :=
  definst "cmc" $ do
    pattern fun => do
      v_6690 <- getRegister cf;
      setRegister cf (notBool_ v_6690);
      pure ()
    pat_end
