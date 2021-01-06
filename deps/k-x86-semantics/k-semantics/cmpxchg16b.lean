def cmpxchg16b : instruction :=
  definst "cmpxchg16b" $ do
    instr_pat $ fun (mem_0 : Mem) =>
     let action : semantics Unit := do
      let v_1 <- evaluateAddress mem_0;
      let v_2 <- getRegister rdx;
      let v_3 <- getRegister rax;
      let v_4 <- eval (concat v_2 v_3);
      let v_5 <- load v_1 16;
      let v_6 <- eval (eq v_4 v_5);
      let v_7 <- getRegister rcx;
      let v_8 <- eval (concat v_7 v_1);
      store v_1 (mux v_6 v_8 v_5) 16;
      let (v_10 : expression (bv 64)) <- eval (extract v_5 0 64);
      let (v_11 : expression (bv 64)) <- eval (extract v_5 64 128);
      setRegister rax (mux v_6 v_3 v_11);
      setRegister rdx (mux v_6 v_2 v_10);
      setRegister zf (eq v_5 v_4);
      pure ()
     action
