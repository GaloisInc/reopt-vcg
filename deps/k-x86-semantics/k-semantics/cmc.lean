def cmc : instruction :=
  definst "cmc" $ do
    instr_pat $
     let action : semantics Unit := do
      let v_0 <- getRegister cf;
      setRegister cf (notBool_ v_0);
      pure ()
     action
