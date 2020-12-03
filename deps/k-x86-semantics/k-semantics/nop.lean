def nop : instruction :=
  definst "nop" $ do
    instr_pat $
     let action : semantics Unit := do
      pure ()
     action
