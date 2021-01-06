def movntpd : instruction :=
  definst "movntpd" $ do
    instr_pat $ fun (xmm_0 : reg (bv 128)) (mem_1 : Mem) =>
     let action : semantics Unit := do
      let v_2 <- evaluateAddress mem_1;
      let v_3 <- getRegister (lhs.of_reg xmm_0);
      store v_2 v_3 16;
      pure ()
     action
