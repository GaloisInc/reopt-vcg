def cld1 : instruction :=
  definst "cld" $ do
    pattern fun => do
      setRegister df (expression.bv_nat 1 0);
      pure ()
    pat_end
