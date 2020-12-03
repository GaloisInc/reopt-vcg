def vmovntps : instruction :=
  definst "vmovntps" $ do
    instr_pat $ fun (xmm_0 : reg (bv 128)) (mem_1 : Mem) =>
     let action : semantics Unit := do
      let v_2 <- evaluateAddress mem_1;
      let v_3 <- getRegister (lhs.of_reg xmm_0);
      store v_2 v_3 16;
      pure ()
     action;
    instr_pat $ fun (ymm_0 : reg (bv 256)) (mem_1 : Mem) =>
     let action : semantics Unit := do
      let v_2 <- evaluateAddress mem_1;
      let v_3 <- getRegister (lhs.of_reg ymm_0);
      store v_2 v_3 32;
      pure ()
     action
