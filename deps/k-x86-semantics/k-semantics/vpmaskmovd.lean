def vpmaskmovd : instruction :=
  definst "vpmaskmovd" $ do
    instr_pat $ fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_3 <- getRegister (lhs.of_reg xmm_1);
      let v_4 <- evaluateAddress mem_0;
      let v_5 <- load v_4 16;
      let (v_6 : expression (bv 32)) <- eval (extract v_5 0 32);
      let (v_7 : expression (bv 32)) <- eval (extract v_5 32 64);
      let (v_8 : expression (bv 32)) <- eval (extract v_5 64 96);
      let (v_9 : expression (bv 32)) <- eval (extract v_5 96 128);
      let v_10 <- eval (concat (mux (isBitSet v_3 64) v_8 (expression.bv_nat 32 0)) (mux (isBitSet v_3 96) v_9 (expression.bv_nat 32 0)));
      let v_11 <- eval (concat (mux (isBitSet v_3 32) v_7 (expression.bv_nat 32 0)) v_10);
      let v_12 <- eval (concat (mux (isBitSet v_3 0) v_6 (expression.bv_nat 32 0)) v_11);
      setRegister (lhs.of_reg xmm_2) v_12;
      pure ()
     action;
    instr_pat $ fun (mem_0 : Mem) (ymm_1 : reg (bv 256)) (ymm_2 : reg (bv 256)) =>
     let action : semantics Unit := do
      let v_3 <- getRegister (lhs.of_reg ymm_1);
      let v_4 <- evaluateAddress mem_0;
      let v_5 <- load v_4 32;
      let (v_6 : expression (bv 32)) <- eval (extract v_5 0 32);
      let (v_7 : expression (bv 32)) <- eval (extract v_5 32 64);
      let (v_8 : expression (bv 32)) <- eval (extract v_5 64 96);
      let (v_9 : expression (bv 32)) <- eval (extract v_5 96 128);
      let (v_10 : expression (bv 32)) <- eval (extract v_5 128 160);
      let (v_11 : expression (bv 32)) <- eval (extract v_5 160 192);
      let (v_12 : expression (bv 32)) <- eval (extract v_5 192 224);
      let (v_13 : expression (bv 32)) <- eval (extract v_5 224 256);
      let v_14 <- eval (concat (mux (isBitSet v_3 192) v_12 (expression.bv_nat 32 0)) (mux (isBitSet v_3 224) v_13 (expression.bv_nat 32 0)));
      let v_15 <- eval (concat (mux (isBitSet v_3 160) v_11 (expression.bv_nat 32 0)) v_14);
      let v_16 <- eval (concat (mux (isBitSet v_3 128) v_10 (expression.bv_nat 32 0)) v_15);
      let v_17 <- eval (concat (mux (isBitSet v_3 96) v_9 (expression.bv_nat 32 0)) v_16);
      let v_18 <- eval (concat (mux (isBitSet v_3 64) v_8 (expression.bv_nat 32 0)) v_17);
      let v_19 <- eval (concat (mux (isBitSet v_3 32) v_7 (expression.bv_nat 32 0)) v_18);
      let v_20 <- eval (concat (mux (isBitSet v_3 0) v_6 (expression.bv_nat 32 0)) v_19);
      setRegister (lhs.of_reg ymm_2) v_20;
      pure ()
     action;
    instr_pat $ fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) (mem_2 : Mem) =>
     let action : semantics Unit := do
      let v_3 <- evaluateAddress mem_2;
      let v_4 <- getRegister (lhs.of_reg xmm_1);
      let v_5 <- getRegister (lhs.of_reg xmm_0);
      let (v_6 : expression (bv 32)) <- eval (extract v_5 0 32);
      let v_7 <- load v_3 16;
      let (v_8 : expression (bv 32)) <- eval (extract v_7 0 32);
      let (v_9 : expression (bv 32)) <- eval (extract v_5 32 64);
      let (v_10 : expression (bv 32)) <- eval (extract v_7 32 64);
      let (v_11 : expression (bv 32)) <- eval (extract v_5 64 96);
      let (v_12 : expression (bv 32)) <- eval (extract v_7 64 96);
      let (v_13 : expression (bv 32)) <- eval (extract v_5 96 128);
      let (v_14 : expression (bv 32)) <- eval (extract v_7 96 128);
      let v_15 <- eval (concat (mux (isBitSet v_4 64) v_11 v_12) (mux (isBitSet v_4 96) v_13 v_14));
      let v_16 <- eval (concat (mux (isBitSet v_4 32) v_9 v_10) v_15);
      let v_17 <- eval (concat (mux (isBitSet v_4 0) v_6 v_8) v_16);
      store v_3 v_17 16;
      pure ()
     action;
    instr_pat $ fun (ymm_0 : reg (bv 256)) (ymm_1 : reg (bv 256)) (mem_2 : Mem) =>
     let action : semantics Unit := do
      let v_3 <- evaluateAddress mem_2;
      let v_4 <- getRegister (lhs.of_reg ymm_1);
      let v_5 <- getRegister (lhs.of_reg ymm_0);
      let (v_6 : expression (bv 32)) <- eval (extract v_5 0 32);
      let v_7 <- load v_3 32;
      let (v_8 : expression (bv 32)) <- eval (extract v_7 0 32);
      let (v_9 : expression (bv 32)) <- eval (extract v_5 32 64);
      let (v_10 : expression (bv 32)) <- eval (extract v_7 32 64);
      let (v_11 : expression (bv 32)) <- eval (extract v_5 64 96);
      let (v_12 : expression (bv 32)) <- eval (extract v_7 64 96);
      let (v_13 : expression (bv 32)) <- eval (extract v_5 96 128);
      let (v_14 : expression (bv 32)) <- eval (extract v_7 96 128);
      let (v_15 : expression (bv 32)) <- eval (extract v_5 128 160);
      let (v_16 : expression (bv 32)) <- eval (extract v_7 128 160);
      let (v_17 : expression (bv 32)) <- eval (extract v_5 160 192);
      let (v_18 : expression (bv 32)) <- eval (extract v_7 160 192);
      let (v_19 : expression (bv 32)) <- eval (extract v_5 192 224);
      let (v_20 : expression (bv 32)) <- eval (extract v_7 192 224);
      let (v_21 : expression (bv 32)) <- eval (extract v_5 224 256);
      let (v_22 : expression (bv 32)) <- eval (extract v_7 224 256);
      let v_23 <- eval (concat (mux (isBitSet v_4 192) v_19 v_20) (mux (isBitSet v_4 224) v_21 v_22));
      let v_24 <- eval (concat (mux (isBitSet v_4 160) v_17 v_18) v_23);
      let v_25 <- eval (concat (mux (isBitSet v_4 128) v_15 v_16) v_24);
      let v_26 <- eval (concat (mux (isBitSet v_4 96) v_13 v_14) v_25);
      let v_27 <- eval (concat (mux (isBitSet v_4 64) v_11 v_12) v_26);
      let v_28 <- eval (concat (mux (isBitSet v_4 32) v_9 v_10) v_27);
      let v_29 <- eval (concat (mux (isBitSet v_4 0) v_6 v_8) v_28);
      store v_3 v_29 32;
      pure ()
     action
