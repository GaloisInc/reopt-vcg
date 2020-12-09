def popw : instruction :=
  definst "popw" $ do
    instr_pat $ fun (mem_0 : Mem) =>
     let action : semantics Unit := do
      let v_1 <- getRegister rsp;
      setRegister rsp (add v_1 (expression.bv_nat 64 2));
      let v_3 <- evaluateAddress mem_0;
      let v_4 <- load v_1 2;
      store v_3 v_4 2;
      pure ()
     action
