def std : instruction :=
  definst "std" $ do
    instr_pat $
     let action : semantics Unit := do
      setRegister df bit_one;
      pure ()
     action
