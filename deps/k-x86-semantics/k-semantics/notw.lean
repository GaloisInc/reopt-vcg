def notw : instruction :=
  definst "notw" $ do
    instr_pat $ fun (mem_0 : Mem) =>
     let action : semantics Unit := do
      let v_1 <- evaluateAddress mem_0;
      let v_2 <- load v_1 2;
      store v_1 (bv_xor v_2 (expression.bv_nat 16 65535)) 2;
      pure ()
     action;
    instr_pat $ fun (r16_0 : reg (bv 16)) =>
     let action : semantics Unit := do
      let v_1 <- getRegister (lhs.of_reg r16_0);
      setRegister (lhs.of_reg r16_0) (bv_xor v_1 (expression.bv_nat 16 65535));
      pure ()
     action
