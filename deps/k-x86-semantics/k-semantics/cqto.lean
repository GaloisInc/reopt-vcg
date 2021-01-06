def cqto : instruction :=
  definst "cqto" $ do
    instr_pat $
     let action : semantics Unit := do
      let v_0 <- getRegister rax;
      let (v_1 : expression (bv 64)) <- eval (extract (sext v_0 128) 0 64);
      setRegister rdx v_1;
      pure ()
     action
