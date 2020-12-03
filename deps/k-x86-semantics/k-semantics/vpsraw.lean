def vpsraw : instruction :=
  definst "vpsraw" $ do
    instr_pat $ fun (imm_0 : imm int) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_3 <- getRegister (lhs.of_reg xmm_1);
      let (v_4 : expression (bv 16)) <- eval (extract v_3 0 16);
      let v_5 <- eval (handleImmediateWithSignExtend imm_0 8 8);
      let v_6 <- eval (concat (expression.bv_nat 56 0) v_5);
      let v_7 <- eval (concat (expression.bv_nat 8 0) v_5);
      let v_8 <- eval (mux (ugt v_6 (expression.bv_nat 64 15)) (expression.bv_nat 16 16) v_7);
      let (v_9 : expression (bv 16)) <- eval (extract v_3 16 32);
      let (v_10 : expression (bv 16)) <- eval (extract v_3 32 48);
      let (v_11 : expression (bv 16)) <- eval (extract v_3 48 64);
      let (v_12 : expression (bv 16)) <- eval (extract v_3 64 80);
      let (v_13 : expression (bv 16)) <- eval (extract v_3 80 96);
      let (v_14 : expression (bv 16)) <- eval (extract v_3 96 112);
      let (v_15 : expression (bv 16)) <- eval (extract v_3 112 128);
      let v_16 <- eval (concat (ashr v_14 v_8) (ashr v_15 v_8));
      let v_17 <- eval (concat (ashr v_13 v_8) v_16);
      let v_18 <- eval (concat (ashr v_12 v_8) v_17);
      let v_19 <- eval (concat (ashr v_11 v_8) v_18);
      let v_20 <- eval (concat (ashr v_10 v_8) v_19);
      let v_21 <- eval (concat (ashr v_9 v_8) v_20);
      let v_22 <- eval (concat (ashr v_4 v_8) v_21);
      setRegister (lhs.of_reg xmm_2) v_22;
      pure ()
     action;
    instr_pat $ fun (imm_0 : imm int) (ymm_1 : reg (bv 256)) (ymm_2 : reg (bv 256)) =>
     let action : semantics Unit := do
      let v_3 <- getRegister (lhs.of_reg ymm_1);
      let (v_4 : expression (bv 16)) <- eval (extract v_3 0 16);
      let v_5 <- eval (handleImmediateWithSignExtend imm_0 8 8);
      let v_6 <- eval (concat (expression.bv_nat 56 0) v_5);
      let v_7 <- eval (concat (expression.bv_nat 8 0) v_5);
      let v_8 <- eval (mux (ugt v_6 (expression.bv_nat 64 15)) (expression.bv_nat 16 16) v_7);
      let (v_9 : expression (bv 16)) <- eval (extract v_3 16 32);
      let (v_10 : expression (bv 16)) <- eval (extract v_3 32 48);
      let (v_11 : expression (bv 16)) <- eval (extract v_3 48 64);
      let (v_12 : expression (bv 16)) <- eval (extract v_3 64 80);
      let (v_13 : expression (bv 16)) <- eval (extract v_3 80 96);
      let (v_14 : expression (bv 16)) <- eval (extract v_3 96 112);
      let (v_15 : expression (bv 16)) <- eval (extract v_3 112 128);
      let (v_16 : expression (bv 16)) <- eval (extract v_3 128 144);
      let (v_17 : expression (bv 16)) <- eval (extract v_3 144 160);
      let (v_18 : expression (bv 16)) <- eval (extract v_3 160 176);
      let (v_19 : expression (bv 16)) <- eval (extract v_3 176 192);
      let (v_20 : expression (bv 16)) <- eval (extract v_3 192 208);
      let (v_21 : expression (bv 16)) <- eval (extract v_3 208 224);
      let (v_22 : expression (bv 16)) <- eval (extract v_3 224 240);
      let (v_23 : expression (bv 16)) <- eval (extract v_3 240 256);
      let v_24 <- eval (concat (ashr v_22 v_8) (ashr v_23 v_8));
      let v_25 <- eval (concat (ashr v_21 v_8) v_24);
      let v_26 <- eval (concat (ashr v_20 v_8) v_25);
      let v_27 <- eval (concat (ashr v_19 v_8) v_26);
      let v_28 <- eval (concat (ashr v_18 v_8) v_27);
      let v_29 <- eval (concat (ashr v_17 v_8) v_28);
      let v_30 <- eval (concat (ashr v_16 v_8) v_29);
      let v_31 <- eval (concat (ashr v_15 v_8) v_30);
      let v_32 <- eval (concat (ashr v_14 v_8) v_31);
      let v_33 <- eval (concat (ashr v_13 v_8) v_32);
      let v_34 <- eval (concat (ashr v_12 v_8) v_33);
      let v_35 <- eval (concat (ashr v_11 v_8) v_34);
      let v_36 <- eval (concat (ashr v_10 v_8) v_35);
      let v_37 <- eval (concat (ashr v_9 v_8) v_36);
      let v_38 <- eval (concat (ashr v_4 v_8) v_37);
      setRegister (lhs.of_reg ymm_2) v_38;
      pure ()
     action;
    instr_pat $ fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_3 <- getRegister (lhs.of_reg xmm_1);
      let (v_4 : expression (bv 16)) <- eval (extract v_3 0 16);
      let v_5 <- evaluateAddress mem_0;
      let v_6 <- load v_5 16;
      let (v_7 : expression (bv 64)) <- eval (extract v_6 64 128);
      let (v_8 : expression (bv 16)) <- eval (extract v_6 112 128);
      let v_9 <- eval (mux (ugt v_7 (expression.bv_nat 64 15)) (expression.bv_nat 16 16) v_8);
      let (v_10 : expression (bv 16)) <- eval (extract v_3 16 32);
      let (v_11 : expression (bv 16)) <- eval (extract v_3 32 48);
      let (v_12 : expression (bv 16)) <- eval (extract v_3 48 64);
      let (v_13 : expression (bv 16)) <- eval (extract v_3 64 80);
      let (v_14 : expression (bv 16)) <- eval (extract v_3 80 96);
      let (v_15 : expression (bv 16)) <- eval (extract v_3 96 112);
      let (v_16 : expression (bv 16)) <- eval (extract v_3 112 128);
      let v_17 <- eval (concat (ashr v_15 v_9) (ashr v_16 v_9));
      let v_18 <- eval (concat (ashr v_14 v_9) v_17);
      let v_19 <- eval (concat (ashr v_13 v_9) v_18);
      let v_20 <- eval (concat (ashr v_12 v_9) v_19);
      let v_21 <- eval (concat (ashr v_11 v_9) v_20);
      let v_22 <- eval (concat (ashr v_10 v_9) v_21);
      let v_23 <- eval (concat (ashr v_4 v_9) v_22);
      setRegister (lhs.of_reg xmm_2) v_23;
      pure ()
     action;
    instr_pat $ fun (mem_0 : Mem) (ymm_1 : reg (bv 256)) (ymm_2 : reg (bv 256)) =>
     let action : semantics Unit := do
      let v_3 <- getRegister (lhs.of_reg ymm_1);
      let (v_4 : expression (bv 16)) <- eval (extract v_3 0 16);
      let v_5 <- evaluateAddress mem_0;
      let v_6 <- load v_5 16;
      let (v_7 : expression (bv 64)) <- eval (extract v_6 64 128);
      let (v_8 : expression (bv 16)) <- eval (extract v_6 112 128);
      let v_9 <- eval (mux (ugt v_7 (expression.bv_nat 64 15)) (expression.bv_nat 16 16) v_8);
      let (v_10 : expression (bv 16)) <- eval (extract v_3 16 32);
      let (v_11 : expression (bv 16)) <- eval (extract v_3 32 48);
      let (v_12 : expression (bv 16)) <- eval (extract v_3 48 64);
      let (v_13 : expression (bv 16)) <- eval (extract v_3 64 80);
      let (v_14 : expression (bv 16)) <- eval (extract v_3 80 96);
      let (v_15 : expression (bv 16)) <- eval (extract v_3 96 112);
      let (v_16 : expression (bv 16)) <- eval (extract v_3 112 128);
      let (v_17 : expression (bv 16)) <- eval (extract v_3 128 144);
      let (v_18 : expression (bv 16)) <- eval (extract v_3 144 160);
      let (v_19 : expression (bv 16)) <- eval (extract v_3 160 176);
      let (v_20 : expression (bv 16)) <- eval (extract v_3 176 192);
      let (v_21 : expression (bv 16)) <- eval (extract v_3 192 208);
      let (v_22 : expression (bv 16)) <- eval (extract v_3 208 224);
      let (v_23 : expression (bv 16)) <- eval (extract v_3 224 240);
      let (v_24 : expression (bv 16)) <- eval (extract v_3 240 256);
      let v_25 <- eval (concat (ashr v_23 v_9) (ashr v_24 v_9));
      let v_26 <- eval (concat (ashr v_22 v_9) v_25);
      let v_27 <- eval (concat (ashr v_21 v_9) v_26);
      let v_28 <- eval (concat (ashr v_20 v_9) v_27);
      let v_29 <- eval (concat (ashr v_19 v_9) v_28);
      let v_30 <- eval (concat (ashr v_18 v_9) v_29);
      let v_31 <- eval (concat (ashr v_17 v_9) v_30);
      let v_32 <- eval (concat (ashr v_16 v_9) v_31);
      let v_33 <- eval (concat (ashr v_15 v_9) v_32);
      let v_34 <- eval (concat (ashr v_14 v_9) v_33);
      let v_35 <- eval (concat (ashr v_13 v_9) v_34);
      let v_36 <- eval (concat (ashr v_12 v_9) v_35);
      let v_37 <- eval (concat (ashr v_11 v_9) v_36);
      let v_38 <- eval (concat (ashr v_10 v_9) v_37);
      let v_39 <- eval (concat (ashr v_4 v_9) v_38);
      setRegister (lhs.of_reg ymm_2) v_39;
      pure ()
     action;
    instr_pat $ fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_3 <- getRegister (lhs.of_reg xmm_1);
      let (v_4 : expression (bv 16)) <- eval (extract v_3 0 16);
      let v_5 <- getRegister (lhs.of_reg xmm_0);
      let (v_6 : expression (bv 64)) <- eval (extract v_5 64 128);
      let (v_7 : expression (bv 16)) <- eval (extract v_5 112 128);
      let v_8 <- eval (mux (ugt v_6 (expression.bv_nat 64 15)) (expression.bv_nat 16 16) v_7);
      let (v_9 : expression (bv 16)) <- eval (extract v_3 16 32);
      let (v_10 : expression (bv 16)) <- eval (extract v_3 32 48);
      let (v_11 : expression (bv 16)) <- eval (extract v_3 48 64);
      let (v_12 : expression (bv 16)) <- eval (extract v_3 64 80);
      let (v_13 : expression (bv 16)) <- eval (extract v_3 80 96);
      let (v_14 : expression (bv 16)) <- eval (extract v_3 96 112);
      let (v_15 : expression (bv 16)) <- eval (extract v_3 112 128);
      let v_16 <- eval (concat (ashr v_14 v_8) (ashr v_15 v_8));
      let v_17 <- eval (concat (ashr v_13 v_8) v_16);
      let v_18 <- eval (concat (ashr v_12 v_8) v_17);
      let v_19 <- eval (concat (ashr v_11 v_8) v_18);
      let v_20 <- eval (concat (ashr v_10 v_8) v_19);
      let v_21 <- eval (concat (ashr v_9 v_8) v_20);
      let v_22 <- eval (concat (ashr v_4 v_8) v_21);
      setRegister (lhs.of_reg xmm_2) v_22;
      pure ()
     action;
    instr_pat $ fun (xmm_0 : reg (bv 128)) (ymm_1 : reg (bv 256)) (ymm_2 : reg (bv 256)) =>
     let action : semantics Unit := do
      let v_3 <- getRegister (lhs.of_reg ymm_1);
      let (v_4 : expression (bv 16)) <- eval (extract v_3 0 16);
      let v_5 <- getRegister (lhs.of_reg xmm_0);
      let (v_6 : expression (bv 64)) <- eval (extract v_5 64 128);
      let (v_7 : expression (bv 16)) <- eval (extract v_5 112 128);
      let v_8 <- eval (mux (ugt v_6 (expression.bv_nat 64 15)) (expression.bv_nat 16 16) v_7);
      let (v_9 : expression (bv 16)) <- eval (extract v_3 16 32);
      let (v_10 : expression (bv 16)) <- eval (extract v_3 32 48);
      let (v_11 : expression (bv 16)) <- eval (extract v_3 48 64);
      let (v_12 : expression (bv 16)) <- eval (extract v_3 64 80);
      let (v_13 : expression (bv 16)) <- eval (extract v_3 80 96);
      let (v_14 : expression (bv 16)) <- eval (extract v_3 96 112);
      let (v_15 : expression (bv 16)) <- eval (extract v_3 112 128);
      let (v_16 : expression (bv 16)) <- eval (extract v_3 128 144);
      let (v_17 : expression (bv 16)) <- eval (extract v_3 144 160);
      let (v_18 : expression (bv 16)) <- eval (extract v_3 160 176);
      let (v_19 : expression (bv 16)) <- eval (extract v_3 176 192);
      let (v_20 : expression (bv 16)) <- eval (extract v_3 192 208);
      let (v_21 : expression (bv 16)) <- eval (extract v_3 208 224);
      let (v_22 : expression (bv 16)) <- eval (extract v_3 224 240);
      let (v_23 : expression (bv 16)) <- eval (extract v_3 240 256);
      let v_24 <- eval (concat (ashr v_22 v_8) (ashr v_23 v_8));
      let v_25 <- eval (concat (ashr v_21 v_8) v_24);
      let v_26 <- eval (concat (ashr v_20 v_8) v_25);
      let v_27 <- eval (concat (ashr v_19 v_8) v_26);
      let v_28 <- eval (concat (ashr v_18 v_8) v_27);
      let v_29 <- eval (concat (ashr v_17 v_8) v_28);
      let v_30 <- eval (concat (ashr v_16 v_8) v_29);
      let v_31 <- eval (concat (ashr v_15 v_8) v_30);
      let v_32 <- eval (concat (ashr v_14 v_8) v_31);
      let v_33 <- eval (concat (ashr v_13 v_8) v_32);
      let v_34 <- eval (concat (ashr v_12 v_8) v_33);
      let v_35 <- eval (concat (ashr v_11 v_8) v_34);
      let v_36 <- eval (concat (ashr v_10 v_8) v_35);
      let v_37 <- eval (concat (ashr v_9 v_8) v_36);
      let v_38 <- eval (concat (ashr v_4 v_8) v_37);
      setRegister (lhs.of_reg ymm_2) v_38;
      pure ()
     action
