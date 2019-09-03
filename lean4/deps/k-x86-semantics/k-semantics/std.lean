def std1 : instruction :=
  definst "std" $ do
    pattern fun => do
      setRegister df (expression.bv_nat 1 1);
      pure ()
    pat_end
