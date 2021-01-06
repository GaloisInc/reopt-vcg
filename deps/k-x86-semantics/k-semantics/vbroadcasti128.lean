def vbroadcasti128 : instruction :=
  definst "vbroadcasti128" $ do
    instr_pat $ fun (mem_0 : Mem) (ymm_1 : reg (bv 256)) =>
     let action : semantics Unit := do
      let v_2 <- evaluateAddress mem_0;
      let v_3 <- load v_2 16;
      let v_4 <- eval (concat v_3 v_3);
      setRegister (lhs.of_reg ymm_1) v_4;
      pure ()
     action
