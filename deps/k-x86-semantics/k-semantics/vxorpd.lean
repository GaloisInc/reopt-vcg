def vxorpd : instruction :=
  definst "vxorpd" $ do
    instr_pat $ fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_3 <- getRegister (lhs.of_reg xmm_1);
      let v_4 <- evaluateAddress mem_0;
      let v_5 <- load v_4 16;
      setRegister (lhs.of_reg xmm_2) (bv_xor v_3 v_5);
      pure ()
     action;
    instr_pat $ fun (mem_0 : Mem) (ymm_1 : reg (bv 256)) (ymm_2 : reg (bv 256)) =>
     let action : semantics Unit := do
      let v_3 <- getRegister (lhs.of_reg ymm_1);
      let v_4 <- evaluateAddress mem_0;
      let v_5 <- load v_4 32;
      setRegister (lhs.of_reg ymm_2) (bv_xor v_3 v_5);
      pure ()
     action
