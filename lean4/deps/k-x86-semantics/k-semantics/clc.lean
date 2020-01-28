def clc : instruction :=
  definst "clc" $ do
    pattern do
      setRegister cf bit_zero;
      pure ()
    pat_end
