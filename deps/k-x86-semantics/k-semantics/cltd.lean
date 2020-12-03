def cltd : instruction :=
  definst "cltd" $ do
    instr_pat $
     let action : semantics Unit := do
      let v_0 <- getRegister rax;
      let (v_1 : expression (bv 32)) <- eval (extract v_0 32 64);
      let (v_2 : expression (bv 32)) <- eval (extract (sext v_1 64) 0 32);
      setRegister edx v_2;
      pure ()
     action
