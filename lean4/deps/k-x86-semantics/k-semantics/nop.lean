def nop : instruction :=
  definst "nop" $ do
    pattern fun => do
      pure ()
    pat_end
