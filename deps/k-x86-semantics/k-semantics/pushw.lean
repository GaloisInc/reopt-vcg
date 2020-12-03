def pushw : instruction :=
  definst "pushw" $ do
    instr_pat $ fun (mem_0 : Mem) =>
     let action : semantics Unit := do
      let v_1 <- getRegister rsp;
      let v_2 <- eval (sub v_1 (expression.bv_nat 64 2));
      let v_3 <- evaluateAddress mem_0;
      let v_4 <- load v_3 2;
      store v_2 v_4 2;
      setRegister rsp v_2;
      pure ()
     action
