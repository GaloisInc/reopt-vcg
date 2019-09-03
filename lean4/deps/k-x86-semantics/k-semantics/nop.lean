def nop1 : instruction :=
  definst "nop" $ do
    pattern fun => do
      pure ()
    pat_end
