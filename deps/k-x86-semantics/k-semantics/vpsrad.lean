def vpsrad : instruction :=
  definst "vpsrad" $ do
    instr_pat $ fun (imm_0 : imm int) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_3 <- getRegister (lhs.of_reg xmm_1);
      let (v_4 : expression (bv 32)) <- eval (extract v_3 0 32);
      let v_5 <- eval (handleImmediateWithSignExtend imm_0 8 8);
      let v_6 <- eval (concat (expression.bv_nat 56 0) v_5);
      let v_7 <- eval (concat (expression.bv_nat 24 0) v_5);
      let v_8 <- eval (mux (ugt v_6 (expression.bv_nat 64 31)) (expression.bv_nat 32 32) v_7);
      let (v_9 : expression (bv 32)) <- eval (extract v_3 32 64);
      let (v_10 : expression (bv 32)) <- eval (extract v_3 64 96);
      let (v_11 : expression (bv 32)) <- eval (extract v_3 96 128);
      let v_12 <- eval (concat (ashr v_10 v_8) (ashr v_11 v_8));
      let v_13 <- eval (concat (ashr v_9 v_8) v_12);
      let v_14 <- eval (concat (ashr v_4 v_8) v_13);
      setRegister (lhs.of_reg xmm_2) v_14;
      pure ()
     action;
    instr_pat $ fun (imm_0 : imm int) (ymm_1 : reg (bv 256)) (ymm_2 : reg (bv 256)) =>
     let action : semantics Unit := do
      let v_3 <- getRegister (lhs.of_reg ymm_1);
      let (v_4 : expression (bv 32)) <- eval (extract v_3 0 32);
      let v_5 <- eval (handleImmediateWithSignExtend imm_0 8 8);
      let v_6 <- eval (concat (expression.bv_nat 56 0) v_5);
      let v_7 <- eval (concat (expression.bv_nat 24 0) v_5);
      let v_8 <- eval (mux (ugt v_6 (expression.bv_nat 64 31)) (expression.bv_nat 32 32) v_7);
      let (v_9 : expression (bv 32)) <- eval (extract v_3 32 64);
      let (v_10 : expression (bv 32)) <- eval (extract v_3 64 96);
      let (v_11 : expression (bv 32)) <- eval (extract v_3 96 128);
      let (v_12 : expression (bv 32)) <- eval (extract v_3 128 160);
      let (v_13 : expression (bv 32)) <- eval (extract v_3 160 192);
      let (v_14 : expression (bv 32)) <- eval (extract v_3 192 224);
      let (v_15 : expression (bv 32)) <- eval (extract v_3 224 256);
      let v_16 <- eval (concat (ashr v_14 v_8) (ashr v_15 v_8));
      let v_17 <- eval (concat (ashr v_13 v_8) v_16);
      let v_18 <- eval (concat (ashr v_12 v_8) v_17);
      let v_19 <- eval (concat (ashr v_11 v_8) v_18);
      let v_20 <- eval (concat (ashr v_10 v_8) v_19);
      let v_21 <- eval (concat (ashr v_9 v_8) v_20);
      let v_22 <- eval (concat (ashr v_4 v_8) v_21);
      setRegister (lhs.of_reg ymm_2) v_22;
      pure ()
     action;
    instr_pat $ fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_3 <- getRegister (lhs.of_reg xmm_1);
      let (v_4 : expression (bv 32)) <- eval (extract v_3 0 32);
      let v_5 <- evaluateAddress mem_0;
      let v_6 <- load v_5 16;
      let (v_7 : expression (bv 64)) <- eval (extract v_6 64 128);
      let (v_8 : expression (bv 32)) <- eval (extract v_6 96 128);
      let v_9 <- eval (mux (ugt v_7 (expression.bv_nat 64 31)) (expression.bv_nat 32 32) v_8);
      let (v_10 : expression (bv 32)) <- eval (extract v_3 32 64);
      let (v_11 : expression (bv 32)) <- eval (extract v_3 64 96);
      let (v_12 : expression (bv 32)) <- eval (extract v_3 96 128);
      let v_13 <- eval (concat (ashr v_11 v_9) (ashr v_12 v_9));
      let v_14 <- eval (concat (ashr v_10 v_9) v_13);
      let v_15 <- eval (concat (ashr v_4 v_9) v_14);
      setRegister (lhs.of_reg xmm_2) v_15;
      pure ()
     action;
    instr_pat $ fun (mem_0 : Mem) (ymm_1 : reg (bv 256)) (ymm_2 : reg (bv 256)) =>
     let action : semantics Unit := do
      let v_3 <- getRegister (lhs.of_reg ymm_1);
      let (v_4 : expression (bv 32)) <- eval (extract v_3 0 32);
      let v_5 <- evaluateAddress mem_0;
      let v_6 <- load v_5 16;
      let (v_7 : expression (bv 64)) <- eval (extract v_6 64 128);
      let (v_8 : expression (bv 32)) <- eval (extract v_6 96 128);
      let v_9 <- eval (mux (ugt v_7 (expression.bv_nat 64 31)) (expression.bv_nat 32 32) v_8);
      let (v_10 : expression (bv 32)) <- eval (extract v_3 32 64);
      let (v_11 : expression (bv 32)) <- eval (extract v_3 64 96);
      let (v_12 : expression (bv 32)) <- eval (extract v_3 96 128);
      let (v_13 : expression (bv 32)) <- eval (extract v_3 128 160);
      let (v_14 : expression (bv 32)) <- eval (extract v_3 160 192);
      let (v_15 : expression (bv 32)) <- eval (extract v_3 192 224);
      let (v_16 : expression (bv 32)) <- eval (extract v_3 224 256);
      let v_17 <- eval (concat (ashr v_15 v_9) (ashr v_16 v_9));
      let v_18 <- eval (concat (ashr v_14 v_9) v_17);
      let v_19 <- eval (concat (ashr v_13 v_9) v_18);
      let v_20 <- eval (concat (ashr v_12 v_9) v_19);
      let v_21 <- eval (concat (ashr v_11 v_9) v_20);
      let v_22 <- eval (concat (ashr v_10 v_9) v_21);
      let v_23 <- eval (concat (ashr v_4 v_9) v_22);
      setRegister (lhs.of_reg ymm_2) v_23;
      pure ()
     action;
    instr_pat $ fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_3 <- getRegister (lhs.of_reg xmm_1);
      let (v_4 : expression (bv 32)) <- eval (extract v_3 0 32);
      let v_5 <- getRegister (lhs.of_reg xmm_0);
      let (v_6 : expression (bv 64)) <- eval (extract v_5 64 128);
      let (v_7 : expression (bv 32)) <- eval (extract v_5 96 128);
      let v_8 <- eval (mux (ugt v_6 (expression.bv_nat 64 31)) (expression.bv_nat 32 32) v_7);
      let (v_9 : expression (bv 32)) <- eval (extract v_3 32 64);
      let (v_10 : expression (bv 32)) <- eval (extract v_3 64 96);
      let (v_11 : expression (bv 32)) <- eval (extract v_3 96 128);
      let v_12 <- eval (concat (ashr v_10 v_8) (ashr v_11 v_8));
      let v_13 <- eval (concat (ashr v_9 v_8) v_12);
      let v_14 <- eval (concat (ashr v_4 v_8) v_13);
      setRegister (lhs.of_reg xmm_2) v_14;
      pure ()
     action;
    instr_pat $ fun (xmm_0 : reg (bv 128)) (ymm_1 : reg (bv 256)) (ymm_2 : reg (bv 256)) =>
     let action : semantics Unit := do
      let v_3 <- getRegister (lhs.of_reg ymm_1);
      let (v_4 : expression (bv 32)) <- eval (extract v_3 0 32);
      let v_5 <- getRegister (lhs.of_reg xmm_0);
      let (v_6 : expression (bv 64)) <- eval (extract v_5 64 128);
      let (v_7 : expression (bv 32)) <- eval (extract v_5 96 128);
      let v_8 <- eval (mux (ugt v_6 (expression.bv_nat 64 31)) (expression.bv_nat 32 32) v_7);
      let (v_9 : expression (bv 32)) <- eval (extract v_3 32 64);
      let (v_10 : expression (bv 32)) <- eval (extract v_3 64 96);
      let (v_11 : expression (bv 32)) <- eval (extract v_3 96 128);
      let (v_12 : expression (bv 32)) <- eval (extract v_3 128 160);
      let (v_13 : expression (bv 32)) <- eval (extract v_3 160 192);
      let (v_14 : expression (bv 32)) <- eval (extract v_3 192 224);
      let (v_15 : expression (bv 32)) <- eval (extract v_3 224 256);
      let v_16 <- eval (concat (ashr v_14 v_8) (ashr v_15 v_8));
      let v_17 <- eval (concat (ashr v_13 v_8) v_16);
      let v_18 <- eval (concat (ashr v_12 v_8) v_17);
      let v_19 <- eval (concat (ashr v_11 v_8) v_18);
      let v_20 <- eval (concat (ashr v_10 v_8) v_19);
      let v_21 <- eval (concat (ashr v_9 v_8) v_20);
      let v_22 <- eval (concat (ashr v_4 v_8) v_21);
      setRegister (lhs.of_reg ymm_2) v_22;
      pure ()
     action
