def std : instruction :=
  definst "std" $ do
    pattern do
      setRegister df bit_one;
      pure ()
    pat_end
