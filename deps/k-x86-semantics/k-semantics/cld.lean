def cld : instruction :=
  definst "cld" $ do
    instr_pat $
     let action : semantics Unit := do
      setRegister df bit_zero;
      pure ()
     action
