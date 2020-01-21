def cld : instruction :=
  definst "cld" $ do
    pattern fun => do
      setRegister df bit_zero;
      pure ()
    pat_end
