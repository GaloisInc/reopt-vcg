def cld : instruction :=
  definst "cld" $ do
    pattern do
      setRegister df bit_zero;
      pure ()
    pat_end
