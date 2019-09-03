def stc1 : instruction :=
  definst "stc" $ do
    pattern fun => do
      setRegister cf (expression.bv_nat 1 1);
      pure ()
    pat_end
