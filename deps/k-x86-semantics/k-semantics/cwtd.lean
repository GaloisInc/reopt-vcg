def cwtd : instruction :=
  definst "cwtd" $ do
    instr_pat $
     let action : semantics Unit := do
      let v_0 <- getRegister rdx;
      let (v_1 : expression (bv 48)) <- eval (extract v_0 0 48);
      let v_2 <- getRegister rax;
      let (v_3 : expression (bv 16)) <- eval (extract v_2 48 64);
      let (v_4 : expression (bv 16)) <- eval (extract (sext v_3 32) 0 16);
      let v_5 <- eval (concat v_1 v_4);
      setRegister rdx v_5;
      pure ()
     action
