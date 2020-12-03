def movl : instruction :=
  definst "movl" $ do
    instr_pat $ fun (imm_0 : imm int) (mem_1 : Mem) =>
     let action : semantics Unit := do
      let v_2 <- evaluateAddress mem_1;
      store v_2 (handleImmediateWithSignExtend imm_0 32 32) 4;
      pure ()
     action;
    instr_pat $ fun (imm_0 : imm int) (r32_1 : reg (bv 32)) =>
     let action : semantics Unit := do
      setRegister (lhs.of_reg r32_1) (handleImmediateWithSignExtend imm_0 32 32);
      pure ()
     action;
    instr_pat $ fun (mem_0 : Mem) (r32_1 : reg (bv 32)) =>
     let action : semantics Unit := do
      let v_2 <- evaluateAddress mem_0;
      let v_3 <- load v_2 4;
      setRegister (lhs.of_reg r32_1) v_3;
      pure ()
     action;
    instr_pat $ fun (r32_0 : reg (bv 32)) (mem_1 : Mem) =>
     let action : semantics Unit := do
      let v_2 <- evaluateAddress mem_1;
      let v_3 <- getRegister (lhs.of_reg r32_0);
      store v_2 v_3 4;
      pure ()
     action;
    instr_pat $ fun (r32_0 : reg (bv 32)) (r32_1 : reg (bv 32)) =>
     let action : semantics Unit := do
      let v_2 <- getRegister (lhs.of_reg r32_0);
      setRegister (lhs.of_reg r32_1) v_2;
      pure ()
     action
