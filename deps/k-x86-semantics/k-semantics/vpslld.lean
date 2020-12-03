def vpslld : instruction :=
  definst "vpslld" $ do
    instr_pat $ fun (imm_0 : imm int) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_3 <- eval (handleImmediateWithSignExtend imm_0 8 8);
      let v_4 <- eval (concat (expression.bv_nat 56 0) v_3);
      let v_5 <- getRegister (lhs.of_reg xmm_1);
      let (v_6 : expression (bv 32)) <- eval (extract v_5 0 32);
      let v_7 <- eval (concat (expression.bv_nat 24 0) v_3);
      let (v_8 : expression (bv 32)) <- eval (extract (shl v_6 v_7) 0 32);
      let (v_9 : expression (bv 32)) <- eval (extract v_5 32 64);
      let (v_10 : expression (bv 32)) <- eval (extract (shl v_9 v_7) 0 32);
      let (v_11 : expression (bv 32)) <- eval (extract v_5 64 96);
      let (v_12 : expression (bv 32)) <- eval (extract (shl v_11 v_7) 0 32);
      let (v_13 : expression (bv 32)) <- eval (extract v_5 96 128);
      let (v_14 : expression (bv 32)) <- eval (extract (shl v_13 v_7) 0 32);
      let v_15 <- eval (concat v_12 v_14);
      let v_16 <- eval (concat v_10 v_15);
      let v_17 <- eval (concat v_8 v_16);
      setRegister (lhs.of_reg xmm_2) (mux (ugt v_4 (expression.bv_nat 64 31)) (expression.bv_nat 128 0) v_17);
      pure ()
     action;
    instr_pat $ fun (imm_0 : imm int) (ymm_1 : reg (bv 256)) (ymm_2 : reg (bv 256)) =>
     let action : semantics Unit := do
      let v_3 <- eval (handleImmediateWithSignExtend imm_0 8 8);
      let v_4 <- eval (concat (expression.bv_nat 56 0) v_3);
      let v_5 <- getRegister (lhs.of_reg ymm_1);
      let (v_6 : expression (bv 32)) <- eval (extract v_5 0 32);
      let v_7 <- eval (concat (expression.bv_nat 24 0) v_3);
      let (v_8 : expression (bv 32)) <- eval (extract (shl v_6 v_7) 0 32);
      let (v_9 : expression (bv 32)) <- eval (extract v_5 32 64);
      let (v_10 : expression (bv 32)) <- eval (extract (shl v_9 v_7) 0 32);
      let (v_11 : expression (bv 32)) <- eval (extract v_5 64 96);
      let (v_12 : expression (bv 32)) <- eval (extract (shl v_11 v_7) 0 32);
      let (v_13 : expression (bv 32)) <- eval (extract v_5 96 128);
      let (v_14 : expression (bv 32)) <- eval (extract (shl v_13 v_7) 0 32);
      let (v_15 : expression (bv 32)) <- eval (extract v_5 128 160);
      let (v_16 : expression (bv 32)) <- eval (extract (shl v_15 v_7) 0 32);
      let (v_17 : expression (bv 32)) <- eval (extract v_5 160 192);
      let (v_18 : expression (bv 32)) <- eval (extract (shl v_17 v_7) 0 32);
      let (v_19 : expression (bv 32)) <- eval (extract v_5 192 224);
      let (v_20 : expression (bv 32)) <- eval (extract (shl v_19 v_7) 0 32);
      let (v_21 : expression (bv 32)) <- eval (extract v_5 224 256);
      let (v_22 : expression (bv 32)) <- eval (extract (shl v_21 v_7) 0 32);
      let v_23 <- eval (concat v_20 v_22);
      let v_24 <- eval (concat v_18 v_23);
      let v_25 <- eval (concat v_16 v_24);
      let v_26 <- eval (concat v_14 v_25);
      let v_27 <- eval (concat v_12 v_26);
      let v_28 <- eval (concat v_10 v_27);
      let v_29 <- eval (concat v_8 v_28);
      setRegister (lhs.of_reg ymm_2) (mux (ugt v_4 (expression.bv_nat 64 31)) (expression.bv_nat 256 0) v_29);
      pure ()
     action;
    instr_pat $ fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_3 <- evaluateAddress mem_0;
      let v_4 <- load v_3 16;
      let (v_5 : expression (bv 64)) <- eval (extract v_4 64 128);
      let v_6 <- getRegister (lhs.of_reg xmm_1);
      let (v_7 : expression (bv 32)) <- eval (extract v_6 0 32);
      let (v_8 : expression (bv 32)) <- eval (extract v_4 96 128);
      let (v_9 : expression (bv 32)) <- eval (extract (shl v_7 v_8) 0 32);
      let (v_10 : expression (bv 32)) <- eval (extract v_6 32 64);
      let (v_11 : expression (bv 32)) <- eval (extract (shl v_10 v_8) 0 32);
      let (v_12 : expression (bv 32)) <- eval (extract v_6 64 96);
      let (v_13 : expression (bv 32)) <- eval (extract (shl v_12 v_8) 0 32);
      let (v_14 : expression (bv 32)) <- eval (extract v_6 96 128);
      let (v_15 : expression (bv 32)) <- eval (extract (shl v_14 v_8) 0 32);
      let v_16 <- eval (concat v_13 v_15);
      let v_17 <- eval (concat v_11 v_16);
      let v_18 <- eval (concat v_9 v_17);
      setRegister (lhs.of_reg xmm_2) (mux (ugt v_5 (expression.bv_nat 64 31)) (expression.bv_nat 128 0) v_18);
      pure ()
     action;
    instr_pat $ fun (mem_0 : Mem) (ymm_1 : reg (bv 256)) (ymm_2 : reg (bv 256)) =>
     let action : semantics Unit := do
      let v_3 <- evaluateAddress mem_0;
      let v_4 <- load v_3 16;
      let (v_5 : expression (bv 64)) <- eval (extract v_4 64 128);
      let v_6 <- getRegister (lhs.of_reg ymm_1);
      let (v_7 : expression (bv 32)) <- eval (extract v_6 0 32);
      let (v_8 : expression (bv 32)) <- eval (extract v_4 96 128);
      let (v_9 : expression (bv 32)) <- eval (extract (shl v_7 v_8) 0 32);
      let (v_10 : expression (bv 32)) <- eval (extract v_6 32 64);
      let (v_11 : expression (bv 32)) <- eval (extract (shl v_10 v_8) 0 32);
      let (v_12 : expression (bv 32)) <- eval (extract v_6 64 96);
      let (v_13 : expression (bv 32)) <- eval (extract (shl v_12 v_8) 0 32);
      let (v_14 : expression (bv 32)) <- eval (extract v_6 96 128);
      let (v_15 : expression (bv 32)) <- eval (extract (shl v_14 v_8) 0 32);
      let (v_16 : expression (bv 32)) <- eval (extract v_6 128 160);
      let (v_17 : expression (bv 32)) <- eval (extract (shl v_16 v_8) 0 32);
      let (v_18 : expression (bv 32)) <- eval (extract v_6 160 192);
      let (v_19 : expression (bv 32)) <- eval (extract (shl v_18 v_8) 0 32);
      let (v_20 : expression (bv 32)) <- eval (extract v_6 192 224);
      let (v_21 : expression (bv 32)) <- eval (extract (shl v_20 v_8) 0 32);
      let (v_22 : expression (bv 32)) <- eval (extract v_6 224 256);
      let (v_23 : expression (bv 32)) <- eval (extract (shl v_22 v_8) 0 32);
      let v_24 <- eval (concat v_21 v_23);
      let v_25 <- eval (concat v_19 v_24);
      let v_26 <- eval (concat v_17 v_25);
      let v_27 <- eval (concat v_15 v_26);
      let v_28 <- eval (concat v_13 v_27);
      let v_29 <- eval (concat v_11 v_28);
      let v_30 <- eval (concat v_9 v_29);
      setRegister (lhs.of_reg ymm_2) (mux (ugt v_5 (expression.bv_nat 64 31)) (expression.bv_nat 256 0) v_30);
      pure ()
     action;
    instr_pat $ fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_3 <- getRegister (lhs.of_reg xmm_0);
      let (v_4 : expression (bv 64)) <- eval (extract v_3 64 128);
      let v_5 <- getRegister (lhs.of_reg xmm_1);
      let (v_6 : expression (bv 32)) <- eval (extract v_5 0 32);
      let (v_7 : expression (bv 32)) <- eval (extract v_3 96 128);
      let (v_8 : expression (bv 32)) <- eval (extract (shl v_6 v_7) 0 32);
      let (v_9 : expression (bv 32)) <- eval (extract v_5 32 64);
      let (v_10 : expression (bv 32)) <- eval (extract (shl v_9 v_7) 0 32);
      let (v_11 : expression (bv 32)) <- eval (extract v_5 64 96);
      let (v_12 : expression (bv 32)) <- eval (extract (shl v_11 v_7) 0 32);
      let (v_13 : expression (bv 32)) <- eval (extract v_5 96 128);
      let (v_14 : expression (bv 32)) <- eval (extract (shl v_13 v_7) 0 32);
      let v_15 <- eval (concat v_12 v_14);
      let v_16 <- eval (concat v_10 v_15);
      let v_17 <- eval (concat v_8 v_16);
      setRegister (lhs.of_reg xmm_2) (mux (ugt v_4 (expression.bv_nat 64 31)) (expression.bv_nat 128 0) v_17);
      pure ()
     action;
    instr_pat $ fun (xmm_0 : reg (bv 128)) (ymm_1 : reg (bv 256)) (ymm_2 : reg (bv 256)) =>
     let action : semantics Unit := do
      let v_3 <- getRegister (lhs.of_reg xmm_0);
      let (v_4 : expression (bv 64)) <- eval (extract v_3 64 128);
      let v_5 <- getRegister (lhs.of_reg ymm_1);
      let (v_6 : expression (bv 32)) <- eval (extract v_5 0 32);
      let (v_7 : expression (bv 32)) <- eval (extract v_3 96 128);
      let (v_8 : expression (bv 32)) <- eval (extract (shl v_6 v_7) 0 32);
      let (v_9 : expression (bv 32)) <- eval (extract v_5 32 64);
      let (v_10 : expression (bv 32)) <- eval (extract (shl v_9 v_7) 0 32);
      let (v_11 : expression (bv 32)) <- eval (extract v_5 64 96);
      let (v_12 : expression (bv 32)) <- eval (extract (shl v_11 v_7) 0 32);
      let (v_13 : expression (bv 32)) <- eval (extract v_5 96 128);
      let (v_14 : expression (bv 32)) <- eval (extract (shl v_13 v_7) 0 32);
      let (v_15 : expression (bv 32)) <- eval (extract v_5 128 160);
      let (v_16 : expression (bv 32)) <- eval (extract (shl v_15 v_7) 0 32);
      let (v_17 : expression (bv 32)) <- eval (extract v_5 160 192);
      let (v_18 : expression (bv 32)) <- eval (extract (shl v_17 v_7) 0 32);
      let (v_19 : expression (bv 32)) <- eval (extract v_5 192 224);
      let (v_20 : expression (bv 32)) <- eval (extract (shl v_19 v_7) 0 32);
      let (v_21 : expression (bv 32)) <- eval (extract v_5 224 256);
      let (v_22 : expression (bv 32)) <- eval (extract (shl v_21 v_7) 0 32);
      let v_23 <- eval (concat v_20 v_22);
      let v_24 <- eval (concat v_18 v_23);
      let v_25 <- eval (concat v_16 v_24);
      let v_26 <- eval (concat v_14 v_25);
      let v_27 <- eval (concat v_12 v_26);
      let v_28 <- eval (concat v_10 v_27);
      let v_29 <- eval (concat v_8 v_28);
      setRegister (lhs.of_reg ymm_2) (mux (ugt v_4 (expression.bv_nat 64 31)) (expression.bv_nat 256 0) v_29);
      pure ()
     action
