def clc : instruction :=
  definst "clc" $ do
    pattern fun => do
      setRegister cf bit_zero;
      pure ()
    pat_end
