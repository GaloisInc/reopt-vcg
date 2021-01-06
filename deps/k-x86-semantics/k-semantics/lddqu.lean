def lddqu : instruction :=
  definst "lddqu" $ do
    instr_pat $ fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_2 <- evaluateAddress mem_0;
      let v_3 <- load v_2 16;
      setRegister (lhs.of_reg xmm_1) v_3;
      pure ()
     action
