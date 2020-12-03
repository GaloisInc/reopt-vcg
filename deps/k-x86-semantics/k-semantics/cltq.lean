def cltq : instruction :=
  definst "cltq" $ do
    instr_pat $
     let action : semantics Unit := do
      let v_0 <- getRegister rax;
      let (v_1 : expression (bv 32)) <- eval (extract v_0 32 64);
      setRegister rax (sext v_1 64);
      pure ()
     action
