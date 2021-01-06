def cmpxchg8b : instruction :=
  definst "cmpxchg8b" $ do
    instr_pat $ fun (mem_0 : Mem) =>
     let action : semantics Unit := do
      let v_1 <- evaluateAddress mem_0;
      let v_2 <- getRegister rdx;
      let (v_3 : expression (bv 32)) <- eval (extract v_2 32 64);
      let v_4 <- getRegister rax;
      let (v_5 : expression (bv 32)) <- eval (extract v_4 32 64);
      let v_6 <- eval (concat v_3 v_5);
      let v_7 <- load v_1 8;
      let v_8 <- eval (eq v_6 v_7);
      let v_9 <- getRegister rcx;
      let (v_10 : expression (bv 32)) <- eval (extract v_9 32 64);
      let (v_11 : expression (bv 32)) <- eval (extract v_1 32 64);
      let v_12 <- eval (concat v_10 v_11);
      store v_1 (mux v_8 v_12 v_7) 8;
      let (v_14 : expression (bv 32)) <- eval (extract v_7 0 32);
      let v_15 <- eval (concat (expression.bv_nat 32 0) v_14);
      let (v_16 : expression (bv 32)) <- eval (extract v_7 32 64);
      let v_17 <- eval (concat (expression.bv_nat 32 0) v_16);
      setRegister rax (mux v_8 v_4 v_17);
      setRegister rdx (mux v_8 v_2 v_15);
      setRegister zf v_8;
      pure ()
     action
