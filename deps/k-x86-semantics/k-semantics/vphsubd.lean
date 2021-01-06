def vphsubd : instruction :=
  definst "vphsubd" $ do
    instr_pat $ fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_3 <- evaluateAddress mem_0;
      let v_4 <- load v_3 16;
      let (v_5 : expression (bv 32)) <- eval (extract v_4 32 64);
      let (v_6 : expression (bv 32)) <- eval (extract v_4 0 32);
      let (v_7 : expression (bv 32)) <- eval (extract v_4 96 128);
      let (v_8 : expression (bv 32)) <- eval (extract v_4 64 96);
      let v_9 <- eval (concat (sub v_5 v_6) (sub v_7 v_8));
      let v_10 <- getRegister (lhs.of_reg xmm_1);
      let (v_11 : expression (bv 32)) <- eval (extract v_10 32 64);
      let (v_12 : expression (bv 32)) <- eval (extract v_10 0 32);
      let v_13 <- eval (concat v_9 (sub v_11 v_12));
      let (v_14 : expression (bv 32)) <- eval (extract v_10 96 128);
      let (v_15 : expression (bv 32)) <- eval (extract v_10 64 96);
      let v_16 <- eval (concat v_13 (sub v_14 v_15));
      setRegister (lhs.of_reg xmm_2) v_16;
      pure ()
     action;
    instr_pat $ fun (mem_0 : Mem) (ymm_1 : reg (bv 256)) (ymm_2 : reg (bv 256)) =>
     let action : semantics Unit := do
      let v_3 <- evaluateAddress mem_0;
      let v_4 <- load v_3 32;
      let (v_5 : expression (bv 32)) <- eval (extract v_4 32 64);
      let (v_6 : expression (bv 32)) <- eval (extract v_4 0 32);
      let (v_7 : expression (bv 32)) <- eval (extract v_4 96 128);
      let (v_8 : expression (bv 32)) <- eval (extract v_4 64 96);
      let v_9 <- eval (concat (sub v_5 v_6) (sub v_7 v_8));
      let v_10 <- getRegister (lhs.of_reg ymm_1);
      let (v_11 : expression (bv 32)) <- eval (extract v_10 32 64);
      let (v_12 : expression (bv 32)) <- eval (extract v_10 0 32);
      let v_13 <- eval (concat v_9 (sub v_11 v_12));
      let (v_14 : expression (bv 32)) <- eval (extract v_10 96 128);
      let (v_15 : expression (bv 32)) <- eval (extract v_10 64 96);
      let v_16 <- eval (concat v_13 (sub v_14 v_15));
      let (v_17 : expression (bv 32)) <- eval (extract v_4 160 192);
      let (v_18 : expression (bv 32)) <- eval (extract v_4 128 160);
      let (v_19 : expression (bv 32)) <- eval (extract v_4 224 256);
      let (v_20 : expression (bv 32)) <- eval (extract v_4 192 224);
      let v_21 <- eval (concat (sub v_17 v_18) (sub v_19 v_20));
      let (v_22 : expression (bv 32)) <- eval (extract v_10 160 192);
      let (v_23 : expression (bv 32)) <- eval (extract v_10 128 160);
      let v_24 <- eval (concat v_21 (sub v_22 v_23));
      let (v_25 : expression (bv 32)) <- eval (extract v_10 224 256);
      let (v_26 : expression (bv 32)) <- eval (extract v_10 192 224);
      let v_27 <- eval (concat v_24 (sub v_25 v_26));
      let v_28 <- eval (concat v_16 v_27);
      setRegister (lhs.of_reg ymm_2) v_28;
      pure ()
     action;
    instr_pat $ fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_3 <- getRegister (lhs.of_reg xmm_0);
      let (v_4 : expression (bv 32)) <- eval (extract v_3 32 64);
      let (v_5 : expression (bv 32)) <- eval (extract v_3 0 32);
      let (v_6 : expression (bv 32)) <- eval (extract v_3 96 128);
      let (v_7 : expression (bv 32)) <- eval (extract v_3 64 96);
      let v_8 <- eval (concat (sub v_4 v_5) (sub v_6 v_7));
      let v_9 <- getRegister (lhs.of_reg xmm_1);
      let (v_10 : expression (bv 32)) <- eval (extract v_9 32 64);
      let (v_11 : expression (bv 32)) <- eval (extract v_9 0 32);
      let v_12 <- eval (concat v_8 (sub v_10 v_11));
      let (v_13 : expression (bv 32)) <- eval (extract v_9 96 128);
      let (v_14 : expression (bv 32)) <- eval (extract v_9 64 96);
      let v_15 <- eval (concat v_12 (sub v_13 v_14));
      setRegister (lhs.of_reg xmm_2) v_15;
      pure ()
     action;
    instr_pat $ fun (ymm_0 : reg (bv 256)) (ymm_1 : reg (bv 256)) (ymm_2 : reg (bv 256)) =>
     let action : semantics Unit := do
      let v_3 <- getRegister (lhs.of_reg ymm_0);
      let (v_4 : expression (bv 32)) <- eval (extract v_3 32 64);
      let (v_5 : expression (bv 32)) <- eval (extract v_3 0 32);
      let (v_6 : expression (bv 32)) <- eval (extract v_3 96 128);
      let (v_7 : expression (bv 32)) <- eval (extract v_3 64 96);
      let v_8 <- eval (concat (sub v_4 v_5) (sub v_6 v_7));
      let v_9 <- getRegister (lhs.of_reg ymm_1);
      let (v_10 : expression (bv 32)) <- eval (extract v_9 32 64);
      let (v_11 : expression (bv 32)) <- eval (extract v_9 0 32);
      let v_12 <- eval (concat v_8 (sub v_10 v_11));
      let (v_13 : expression (bv 32)) <- eval (extract v_9 96 128);
      let (v_14 : expression (bv 32)) <- eval (extract v_9 64 96);
      let v_15 <- eval (concat v_12 (sub v_13 v_14));
      let (v_16 : expression (bv 32)) <- eval (extract v_3 160 192);
      let (v_17 : expression (bv 32)) <- eval (extract v_3 128 160);
      let (v_18 : expression (bv 32)) <- eval (extract v_3 224 256);
      let (v_19 : expression (bv 32)) <- eval (extract v_3 192 224);
      let v_20 <- eval (concat (sub v_16 v_17) (sub v_18 v_19));
      let (v_21 : expression (bv 32)) <- eval (extract v_9 160 192);
      let (v_22 : expression (bv 32)) <- eval (extract v_9 128 160);
      let v_23 <- eval (concat v_20 (sub v_21 v_22));
      let (v_24 : expression (bv 32)) <- eval (extract v_9 224 256);
      let (v_25 : expression (bv 32)) <- eval (extract v_9 192 224);
      let v_26 <- eval (concat v_23 (sub v_24 v_25));
      let v_27 <- eval (concat v_15 v_26);
      setRegister (lhs.of_reg ymm_2) v_27;
      pure ()
     action
