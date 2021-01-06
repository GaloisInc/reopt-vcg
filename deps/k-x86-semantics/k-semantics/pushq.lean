def pushq : instruction :=
  definst "pushq" $ do
    instr_pat $ fun (imm_0 : imm int) =>
     let action : semantics Unit := do
      let v_1 <- getRegister rsp;
      let v_2 <- eval (sub v_1 (expression.bv_nat 64 8));
      store v_2 (handleImmediateWithSignExtend imm_0 32 64) 8;
      setRegister rsp v_2;
      pure ()
     action;
    instr_pat $ fun (mem_0 : Mem) =>
     let action : semantics Unit := do
      let v_1 <- getRegister rsp;
      let v_2 <- eval (sub v_1 (expression.bv_nat 64 8));
      let v_3 <- evaluateAddress mem_0;
      let v_4 <- load v_3 8;
      store v_2 v_4 8;
      setRegister rsp v_2;
      pure ()
     action
