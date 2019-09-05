def stc1 : instruction :=
  definst "stc" $ do
    pattern fun => do
      setRegister cf bit_one;
      pure ()
    pat_end
