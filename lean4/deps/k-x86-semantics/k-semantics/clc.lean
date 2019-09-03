def clc1 : instruction :=
  definst "clc" $ do
    pattern fun => do
      setRegister cf (expression.bv_nat 1 0);
      pure ()
    pat_end
