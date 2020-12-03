def notl : instruction :=
  definst "notl" $ do
    instr_pat $ fun (mem_0 : Mem) =>
     let action : semantics Unit := do
      let v_1 <- evaluateAddress mem_0;
      let v_2 <- load v_1 4;
      store v_1 (bv_xor v_2 (expression.bv_nat 32 4294967295)) 4;
      pure ()
     action;
    instr_pat $ fun (r32_0 : reg (bv 32)) =>
     let action : semantics Unit := do
      let v_1 <- getRegister (lhs.of_reg r32_0);
      setRegister (lhs.of_reg r32_0) (bv_xor v_1 (expression.bv_nat 32 4294967295));
      pure ()
     action
