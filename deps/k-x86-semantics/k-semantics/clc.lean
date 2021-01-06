def clc : instruction :=
  definst "clc" $ do
    instr_pat $
     let action : semantics Unit := do
      setRegister cf bit_zero;
      pure ()
     action
