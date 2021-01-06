def stc : instruction :=
  definst "stc" $ do
    instr_pat $
     let action : semantics Unit := do
      setRegister cf bit_one;
      pure ()
     action
