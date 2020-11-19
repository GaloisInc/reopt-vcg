def stc : instruction :=
  definst "stc" $ do
    pattern do
      setRegister cf bit_one;
      pure ()
    pat_end
