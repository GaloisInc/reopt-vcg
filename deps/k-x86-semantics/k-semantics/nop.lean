def nop : instruction :=
  definst "nop" $ do
    pattern do
      pure ()
    pat_end
