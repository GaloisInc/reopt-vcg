def std : instruction :=
  definst "std" $ do
    pattern fun => do
      setRegister df bit_one;
      pure ()
    pat_end
