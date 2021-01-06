def vinsertf128 : instruction :=
  definst "vinsertf128" $ do
    instr_pat $ fun (imm_0 : imm int) (mem_1 : Mem) (ymm_2 : reg (bv 256)) (ymm_3 : reg (bv 256)) =>
     let action : semantics Unit := do
      let v_4 <- getRegister (lhs.of_reg ymm_2);
      let (v_5 : expression (bv 128)) <- eval (extract v_4 0 128);
      let v_6 <- evaluateAddress mem_1;
      let v_7 <- load v_6 16;
      let v_8 <- eval (concat v_5 v_7);
      let (v_9 : expression (bv 128)) <- eval (extract v_4 128 256);
      let v_10 <- eval (concat v_7 v_9);
      setRegister (lhs.of_reg ymm_3) (mux (isBitClear (handleImmediateWithSignExtend imm_0 8 8) 7) v_8 v_10);
      pure ()
     action;
    instr_pat $ fun (imm_0 : imm int) (xmm_1 : reg (bv 128)) (ymm_2 : reg (bv 256)) (ymm_3 : reg (bv 256)) =>
     let action : semantics Unit := do
      let v_4 <- getRegister (lhs.of_reg ymm_2);
      let (v_5 : expression (bv 128)) <- eval (extract v_4 0 128);
      let v_6 <- getRegister (lhs.of_reg xmm_1);
      let v_7 <- eval (concat v_5 v_6);
      let (v_8 : expression (bv 128)) <- eval (extract v_4 128 256);
      let v_9 <- eval (concat v_6 v_8);
      setRegister (lhs.of_reg ymm_3) (mux (isBitClear (handleImmediateWithSignExtend imm_0 8 8) 7) v_7 v_9);
      pure ()
     action
