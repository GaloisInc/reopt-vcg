def cwtl : instruction :=
  definst "cwtl" $ do
    instr_pat $
     let action : semantics Unit := do
      let v_0 <- getRegister rax;
      let (v_1 : expression (bv 16)) <- eval (extract v_0 48 64);
      setRegister eax (sext v_1 32);
      pure ()
     action
