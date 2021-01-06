def movw : instruction :=
  definst "movw" $ do
    instr_pat $ fun (imm_0 : imm int) (mem_1 : Mem) =>
     let action : semantics Unit := do
      let v_2 <- evaluateAddress mem_1;
      store v_2 (handleImmediateWithSignExtend imm_0 16 16) 2;
      pure ()
     action;
    instr_pat $ fun (imm_0 : imm int) (r16_1 : reg (bv 16)) =>
     let action : semantics Unit := do
      setRegister (lhs.of_reg r16_1) (handleImmediateWithSignExtend imm_0 16 16);
      pure ()
     action;
    instr_pat $ fun (mem_0 : Mem) (r16_1 : reg (bv 16)) =>
     let action : semantics Unit := do
      let v_2 <- evaluateAddress mem_0;
      let v_3 <- load v_2 2;
      setRegister (lhs.of_reg r16_1) v_3;
      pure ()
     action;
    instr_pat $ fun (r16_0 : reg (bv 16)) (mem_1 : Mem) =>
     let action : semantics Unit := do
      let v_2 <- evaluateAddress mem_1;
      let v_3 <- getRegister (lhs.of_reg r16_0);
      store v_2 v_3 2;
      pure ()
     action;
    instr_pat $ fun (r16_0 : reg (bv 16)) (r16_1 : reg (bv 16)) =>
     let action : semantics Unit := do
      let v_2 <- getRegister (lhs.of_reg r16_0);
      setRegister (lhs.of_reg r16_1) v_2;
      pure ()
     action
