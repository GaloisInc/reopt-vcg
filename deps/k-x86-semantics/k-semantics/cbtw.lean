def cbtw : instruction :=
  definst "cbtw" $ do
    instr_pat $
     let action : semantics Unit := do
      let v_0 <- getRegister rax;
      let (v_1 : expression (bv 48)) <- eval (extract v_0 0 48);
      let (v_2 : expression (bv 8)) <- eval (extract v_0 56 64);
      let v_3 <- eval (concat v_1 (sext v_2 16));
      setRegister rax v_3;
      pure ()
     action
