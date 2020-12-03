def vpermilpd : instruction :=
  definst "vpermilpd" $ do
    instr_pat $ fun (imm_0 : imm int) (mem_1 : Mem) (xmm_2 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_3 <- eval (handleImmediateWithSignExtend imm_0 8 8);
      let v_4 <- evaluateAddress mem_1;
      let v_5 <- load v_4 16;
      let (v_6 : expression (bv 64)) <- eval (extract v_5 64 128);
      let (v_7 : expression (bv 64)) <- eval (extract v_5 0 64);
      let v_8 <- eval (concat (mux (isBitClear v_3 6) v_6 v_7) (mux (isBitClear v_3 7) v_6 v_7));
      setRegister (lhs.of_reg xmm_2) v_8;
      pure ()
     action;
    instr_pat $ fun (imm_0 : imm int) (mem_1 : Mem) (ymm_2 : reg (bv 256)) =>
     let action : semantics Unit := do
      let v_3 <- eval (handleImmediateWithSignExtend imm_0 8 8);
      let v_4 <- evaluateAddress mem_1;
      let v_5 <- load v_4 32;
      let (v_6 : expression (bv 64)) <- eval (extract v_5 64 128);
      let (v_7 : expression (bv 64)) <- eval (extract v_5 0 64);
      let (v_8 : expression (bv 64)) <- eval (extract v_5 192 256);
      let (v_9 : expression (bv 64)) <- eval (extract v_5 128 192);
      let v_10 <- eval (concat (mux (isBitClear v_3 6) v_8 v_9) (mux (isBitClear v_3 7) v_8 v_9));
      let v_11 <- eval (concat (mux (isBitClear v_3 5) v_6 v_7) v_10);
      let v_12 <- eval (concat (mux (isBitClear v_3 4) v_6 v_7) v_11);
      setRegister (lhs.of_reg ymm_2) v_12;
      pure ()
     action;
    instr_pat $ fun (imm_0 : imm int) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_3 <- eval (handleImmediateWithSignExtend imm_0 8 8);
      let v_4 <- getRegister (lhs.of_reg xmm_1);
      let (v_5 : expression (bv 64)) <- eval (extract v_4 64 128);
      let (v_6 : expression (bv 64)) <- eval (extract v_4 0 64);
      let v_7 <- eval (concat (mux (isBitClear v_3 6) v_5 v_6) (mux (isBitClear v_3 7) v_5 v_6));
      setRegister (lhs.of_reg xmm_2) v_7;
      pure ()
     action;
    instr_pat $ fun (imm_0 : imm int) (ymm_1 : reg (bv 256)) (ymm_2 : reg (bv 256)) =>
     let action : semantics Unit := do
      let v_3 <- eval (handleImmediateWithSignExtend imm_0 8 8);
      let v_4 <- getRegister (lhs.of_reg ymm_1);
      let (v_5 : expression (bv 64)) <- eval (extract v_4 64 128);
      let (v_6 : expression (bv 64)) <- eval (extract v_4 0 64);
      let (v_7 : expression (bv 64)) <- eval (extract v_4 192 256);
      let (v_8 : expression (bv 64)) <- eval (extract v_4 128 192);
      let v_9 <- eval (concat (mux (isBitClear v_3 6) v_7 v_8) (mux (isBitClear v_3 7) v_7 v_8));
      let v_10 <- eval (concat (mux (isBitClear v_3 5) v_5 v_6) v_9);
      let v_11 <- eval (concat (mux (isBitClear v_3 4) v_5 v_6) v_10);
      setRegister (lhs.of_reg ymm_2) v_11;
      pure ()
     action;
    instr_pat $ fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_3 <- evaluateAddress mem_0;
      let v_4 <- load v_3 16;
      let v_5 <- getRegister (lhs.of_reg xmm_1);
      let (v_6 : expression (bv 64)) <- eval (extract v_5 64 128);
      let (v_7 : expression (bv 64)) <- eval (extract v_5 0 64);
      let v_8 <- eval (concat (mux (isBitClear v_4 62) v_6 v_7) (mux (isBitClear v_4 126) v_6 v_7));
      setRegister (lhs.of_reg xmm_2) v_8;
      pure ()
     action;
    instr_pat $ fun (mem_0 : Mem) (ymm_1 : reg (bv 256)) (ymm_2 : reg (bv 256)) =>
     let action : semantics Unit := do
      let v_3 <- evaluateAddress mem_0;
      let v_4 <- load v_3 32;
      let v_5 <- getRegister (lhs.of_reg ymm_1);
      let (v_6 : expression (bv 64)) <- eval (extract v_5 64 128);
      let (v_7 : expression (bv 64)) <- eval (extract v_5 0 64);
      let (v_8 : expression (bv 64)) <- eval (extract v_5 192 256);
      let (v_9 : expression (bv 64)) <- eval (extract v_5 128 192);
      let v_10 <- eval (concat (mux (isBitClear v_4 190) v_8 v_9) (mux (isBitClear v_4 254) v_8 v_9));
      let v_11 <- eval (concat (mux (isBitClear v_4 126) v_6 v_7) v_10);
      let v_12 <- eval (concat (mux (isBitClear v_4 62) v_6 v_7) v_11);
      setRegister (lhs.of_reg ymm_2) v_12;
      pure ()
     action;
    instr_pat $ fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_3 <- getRegister (lhs.of_reg xmm_0);
      let v_4 <- getRegister (lhs.of_reg xmm_1);
      let (v_5 : expression (bv 64)) <- eval (extract v_4 64 128);
      let (v_6 : expression (bv 64)) <- eval (extract v_4 0 64);
      let v_7 <- eval (concat (mux (isBitClear v_3 62) v_5 v_6) (mux (isBitClear v_3 126) v_5 v_6));
      setRegister (lhs.of_reg xmm_2) v_7;
      pure ()
     action;
    instr_pat $ fun (ymm_0 : reg (bv 256)) (ymm_1 : reg (bv 256)) (ymm_2 : reg (bv 256)) =>
     let action : semantics Unit := do
      let v_3 <- getRegister (lhs.of_reg ymm_0);
      let v_4 <- getRegister (lhs.of_reg ymm_1);
      let (v_5 : expression (bv 64)) <- eval (extract v_4 64 128);
      let (v_6 : expression (bv 64)) <- eval (extract v_4 0 64);
      let (v_7 : expression (bv 64)) <- eval (extract v_4 192 256);
      let (v_8 : expression (bv 64)) <- eval (extract v_4 128 192);
      let v_9 <- eval (concat (mux (isBitClear v_3 190) v_7 v_8) (mux (isBitClear v_3 254) v_7 v_8));
      let v_10 <- eval (concat (mux (isBitClear v_3 126) v_5 v_6) v_9);
      let v_11 <- eval (concat (mux (isBitClear v_3 62) v_5 v_6) v_10);
      setRegister (lhs.of_reg ymm_2) v_11;
      pure ()
     action
