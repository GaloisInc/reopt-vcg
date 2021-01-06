def movnti : instruction :=
  definst "movnti" $ do
    instr_pat $ fun (r32_0 : reg (bv 32)) (mem_1 : Mem) =>
     let action : semantics Unit := do
      let v_2 <- evaluateAddress mem_1;
      let v_3 <- getRegister (lhs.of_reg r32_0);
      store v_2 v_3 4;
      pure ()
     action;
    instr_pat $ fun (r64_0 : reg (bv 64)) (mem_1 : Mem) =>
     let action : semantics Unit := do
      let v_2 <- evaluateAddress mem_1;
      let v_3 <- getRegister (lhs.of_reg r64_0);
      store v_2 v_3 8;
      pure ()
     action
