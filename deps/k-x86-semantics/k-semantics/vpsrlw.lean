def vpsrlw : instruction :=
  definst "vpsrlw" $ do
    instr_pat $ fun (imm_0 : imm int) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_3 <- eval (handleImmediateWithSignExtend imm_0 8 8);
      let v_4 <- eval (concat (expression.bv_nat 56 0) v_3);
      let v_5 <- getRegister (lhs.of_reg xmm_1);
      let (v_6 : expression (bv 16)) <- eval (extract v_5 0 16);
      let v_7 <- eval (concat (expression.bv_nat 8 0) v_3);
      let (v_8 : expression (bv 16)) <- eval (extract v_5 16 32);
      let (v_9 : expression (bv 16)) <- eval (extract v_5 32 48);
      let (v_10 : expression (bv 16)) <- eval (extract v_5 48 64);
      let (v_11 : expression (bv 16)) <- eval (extract v_5 64 80);
      let (v_12 : expression (bv 16)) <- eval (extract v_5 80 96);
      let (v_13 : expression (bv 16)) <- eval (extract v_5 96 112);
      let (v_14 : expression (bv 16)) <- eval (extract v_5 112 128);
      let v_15 <- eval (concat (lshr v_13 v_7) (lshr v_14 v_7));
      let v_16 <- eval (concat (lshr v_12 v_7) v_15);
      let v_17 <- eval (concat (lshr v_11 v_7) v_16);
      let v_18 <- eval (concat (lshr v_10 v_7) v_17);
      let v_19 <- eval (concat (lshr v_9 v_7) v_18);
      let v_20 <- eval (concat (lshr v_8 v_7) v_19);
      let v_21 <- eval (concat (lshr v_6 v_7) v_20);
      setRegister (lhs.of_reg xmm_2) (mux (ugt v_4 (expression.bv_nat 64 15)) (expression.bv_nat 128 0) v_21);
      pure ()
     action;
    instr_pat $ fun (imm_0 : imm int) (ymm_1 : reg (bv 256)) (ymm_2 : reg (bv 256)) =>
     let action : semantics Unit := do
      let v_3 <- eval (handleImmediateWithSignExtend imm_0 8 8);
      let v_4 <- eval (concat (expression.bv_nat 56 0) v_3);
      let v_5 <- getRegister (lhs.of_reg ymm_1);
      let (v_6 : expression (bv 16)) <- eval (extract v_5 0 16);
      let v_7 <- eval (concat (expression.bv_nat 8 0) v_3);
      let (v_8 : expression (bv 16)) <- eval (extract v_5 16 32);
      let (v_9 : expression (bv 16)) <- eval (extract v_5 32 48);
      let (v_10 : expression (bv 16)) <- eval (extract v_5 48 64);
      let (v_11 : expression (bv 16)) <- eval (extract v_5 64 80);
      let (v_12 : expression (bv 16)) <- eval (extract v_5 80 96);
      let (v_13 : expression (bv 16)) <- eval (extract v_5 96 112);
      let (v_14 : expression (bv 16)) <- eval (extract v_5 112 128);
      let (v_15 : expression (bv 16)) <- eval (extract v_5 128 144);
      let (v_16 : expression (bv 16)) <- eval (extract v_5 144 160);
      let (v_17 : expression (bv 16)) <- eval (extract v_5 160 176);
      let (v_18 : expression (bv 16)) <- eval (extract v_5 176 192);
      let (v_19 : expression (bv 16)) <- eval (extract v_5 192 208);
      let (v_20 : expression (bv 16)) <- eval (extract v_5 208 224);
      let (v_21 : expression (bv 16)) <- eval (extract v_5 224 240);
      let (v_22 : expression (bv 16)) <- eval (extract v_5 240 256);
      let v_23 <- eval (concat (lshr v_21 v_7) (lshr v_22 v_7));
      let v_24 <- eval (concat (lshr v_20 v_7) v_23);
      let v_25 <- eval (concat (lshr v_19 v_7) v_24);
      let v_26 <- eval (concat (lshr v_18 v_7) v_25);
      let v_27 <- eval (concat (lshr v_17 v_7) v_26);
      let v_28 <- eval (concat (lshr v_16 v_7) v_27);
      let v_29 <- eval (concat (lshr v_15 v_7) v_28);
      let v_30 <- eval (concat (lshr v_14 v_7) v_29);
      let v_31 <- eval (concat (lshr v_13 v_7) v_30);
      let v_32 <- eval (concat (lshr v_12 v_7) v_31);
      let v_33 <- eval (concat (lshr v_11 v_7) v_32);
      let v_34 <- eval (concat (lshr v_10 v_7) v_33);
      let v_35 <- eval (concat (lshr v_9 v_7) v_34);
      let v_36 <- eval (concat (lshr v_8 v_7) v_35);
      let v_37 <- eval (concat (lshr v_6 v_7) v_36);
      setRegister (lhs.of_reg ymm_2) (mux (ugt v_4 (expression.bv_nat 64 15)) (expression.bv_nat 256 0) v_37);
      pure ()
     action;
    instr_pat $ fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_3 <- evaluateAddress mem_0;
      let v_4 <- load v_3 16;
      let (v_5 : expression (bv 64)) <- eval (extract v_4 64 128);
      let v_6 <- getRegister (lhs.of_reg xmm_1);
      let (v_7 : expression (bv 16)) <- eval (extract v_6 0 16);
      let (v_8 : expression (bv 16)) <- eval (extract v_4 112 128);
      let (v_9 : expression (bv 16)) <- eval (extract v_6 16 32);
      let (v_10 : expression (bv 16)) <- eval (extract v_6 32 48);
      let (v_11 : expression (bv 16)) <- eval (extract v_6 48 64);
      let (v_12 : expression (bv 16)) <- eval (extract v_6 64 80);
      let (v_13 : expression (bv 16)) <- eval (extract v_6 80 96);
      let (v_14 : expression (bv 16)) <- eval (extract v_6 96 112);
      let (v_15 : expression (bv 16)) <- eval (extract v_6 112 128);
      let v_16 <- eval (concat (lshr v_14 v_8) (lshr v_15 v_8));
      let v_17 <- eval (concat (lshr v_13 v_8) v_16);
      let v_18 <- eval (concat (lshr v_12 v_8) v_17);
      let v_19 <- eval (concat (lshr v_11 v_8) v_18);
      let v_20 <- eval (concat (lshr v_10 v_8) v_19);
      let v_21 <- eval (concat (lshr v_9 v_8) v_20);
      let v_22 <- eval (concat (lshr v_7 v_8) v_21);
      setRegister (lhs.of_reg xmm_2) (mux (ugt v_5 (expression.bv_nat 64 15)) (expression.bv_nat 128 0) v_22);
      pure ()
     action;
    instr_pat $ fun (mem_0 : Mem) (ymm_1 : reg (bv 256)) (ymm_2 : reg (bv 256)) =>
     let action : semantics Unit := do
      let v_3 <- evaluateAddress mem_0;
      let v_4 <- load v_3 16;
      let (v_5 : expression (bv 64)) <- eval (extract v_4 64 128);
      let v_6 <- getRegister (lhs.of_reg ymm_1);
      let (v_7 : expression (bv 16)) <- eval (extract v_6 0 16);
      let (v_8 : expression (bv 16)) <- eval (extract v_4 112 128);
      let (v_9 : expression (bv 16)) <- eval (extract v_6 16 32);
      let (v_10 : expression (bv 16)) <- eval (extract v_6 32 48);
      let (v_11 : expression (bv 16)) <- eval (extract v_6 48 64);
      let (v_12 : expression (bv 16)) <- eval (extract v_6 64 80);
      let (v_13 : expression (bv 16)) <- eval (extract v_6 80 96);
      let (v_14 : expression (bv 16)) <- eval (extract v_6 96 112);
      let (v_15 : expression (bv 16)) <- eval (extract v_6 112 128);
      let (v_16 : expression (bv 16)) <- eval (extract v_6 128 144);
      let (v_17 : expression (bv 16)) <- eval (extract v_6 144 160);
      let (v_18 : expression (bv 16)) <- eval (extract v_6 160 176);
      let (v_19 : expression (bv 16)) <- eval (extract v_6 176 192);
      let (v_20 : expression (bv 16)) <- eval (extract v_6 192 208);
      let (v_21 : expression (bv 16)) <- eval (extract v_6 208 224);
      let (v_22 : expression (bv 16)) <- eval (extract v_6 224 240);
      let (v_23 : expression (bv 16)) <- eval (extract v_6 240 256);
      let v_24 <- eval (concat (lshr v_22 v_8) (lshr v_23 v_8));
      let v_25 <- eval (concat (lshr v_21 v_8) v_24);
      let v_26 <- eval (concat (lshr v_20 v_8) v_25);
      let v_27 <- eval (concat (lshr v_19 v_8) v_26);
      let v_28 <- eval (concat (lshr v_18 v_8) v_27);
      let v_29 <- eval (concat (lshr v_17 v_8) v_28);
      let v_30 <- eval (concat (lshr v_16 v_8) v_29);
      let v_31 <- eval (concat (lshr v_15 v_8) v_30);
      let v_32 <- eval (concat (lshr v_14 v_8) v_31);
      let v_33 <- eval (concat (lshr v_13 v_8) v_32);
      let v_34 <- eval (concat (lshr v_12 v_8) v_33);
      let v_35 <- eval (concat (lshr v_11 v_8) v_34);
      let v_36 <- eval (concat (lshr v_10 v_8) v_35);
      let v_37 <- eval (concat (lshr v_9 v_8) v_36);
      let v_38 <- eval (concat (lshr v_7 v_8) v_37);
      setRegister (lhs.of_reg ymm_2) (mux (ugt v_5 (expression.bv_nat 64 15)) (expression.bv_nat 256 0) v_38);
      pure ()
     action;
    instr_pat $ fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_3 <- getRegister (lhs.of_reg xmm_0);
      let (v_4 : expression (bv 64)) <- eval (extract v_3 64 128);
      let v_5 <- getRegister (lhs.of_reg xmm_1);
      let (v_6 : expression (bv 16)) <- eval (extract v_5 0 16);
      let (v_7 : expression (bv 16)) <- eval (extract v_3 112 128);
      let (v_8 : expression (bv 16)) <- eval (extract v_5 16 32);
      let (v_9 : expression (bv 16)) <- eval (extract v_5 32 48);
      let (v_10 : expression (bv 16)) <- eval (extract v_5 48 64);
      let (v_11 : expression (bv 16)) <- eval (extract v_5 64 80);
      let (v_12 : expression (bv 16)) <- eval (extract v_5 80 96);
      let (v_13 : expression (bv 16)) <- eval (extract v_5 96 112);
      let (v_14 : expression (bv 16)) <- eval (extract v_5 112 128);
      let v_15 <- eval (concat (lshr v_13 v_7) (lshr v_14 v_7));
      let v_16 <- eval (concat (lshr v_12 v_7) v_15);
      let v_17 <- eval (concat (lshr v_11 v_7) v_16);
      let v_18 <- eval (concat (lshr v_10 v_7) v_17);
      let v_19 <- eval (concat (lshr v_9 v_7) v_18);
      let v_20 <- eval (concat (lshr v_8 v_7) v_19);
      let v_21 <- eval (concat (lshr v_6 v_7) v_20);
      setRegister (lhs.of_reg xmm_2) (mux (ugt v_4 (expression.bv_nat 64 15)) (expression.bv_nat 128 0) v_21);
      pure ()
     action;
    instr_pat $ fun (xmm_0 : reg (bv 128)) (ymm_1 : reg (bv 256)) (ymm_2 : reg (bv 256)) =>
     let action : semantics Unit := do
      let v_3 <- getRegister (lhs.of_reg xmm_0);
      let (v_4 : expression (bv 64)) <- eval (extract v_3 64 128);
      let v_5 <- getRegister (lhs.of_reg ymm_1);
      let (v_6 : expression (bv 16)) <- eval (extract v_5 0 16);
      let (v_7 : expression (bv 16)) <- eval (extract v_3 112 128);
      let (v_8 : expression (bv 16)) <- eval (extract v_5 16 32);
      let (v_9 : expression (bv 16)) <- eval (extract v_5 32 48);
      let (v_10 : expression (bv 16)) <- eval (extract v_5 48 64);
      let (v_11 : expression (bv 16)) <- eval (extract v_5 64 80);
      let (v_12 : expression (bv 16)) <- eval (extract v_5 80 96);
      let (v_13 : expression (bv 16)) <- eval (extract v_5 96 112);
      let (v_14 : expression (bv 16)) <- eval (extract v_5 112 128);
      let (v_15 : expression (bv 16)) <- eval (extract v_5 128 144);
      let (v_16 : expression (bv 16)) <- eval (extract v_5 144 160);
      let (v_17 : expression (bv 16)) <- eval (extract v_5 160 176);
      let (v_18 : expression (bv 16)) <- eval (extract v_5 176 192);
      let (v_19 : expression (bv 16)) <- eval (extract v_5 192 208);
      let (v_20 : expression (bv 16)) <- eval (extract v_5 208 224);
      let (v_21 : expression (bv 16)) <- eval (extract v_5 224 240);
      let (v_22 : expression (bv 16)) <- eval (extract v_5 240 256);
      let v_23 <- eval (concat (lshr v_21 v_7) (lshr v_22 v_7));
      let v_24 <- eval (concat (lshr v_20 v_7) v_23);
      let v_25 <- eval (concat (lshr v_19 v_7) v_24);
      let v_26 <- eval (concat (lshr v_18 v_7) v_25);
      let v_27 <- eval (concat (lshr v_17 v_7) v_26);
      let v_28 <- eval (concat (lshr v_16 v_7) v_27);
      let v_29 <- eval (concat (lshr v_15 v_7) v_28);
      let v_30 <- eval (concat (lshr v_14 v_7) v_29);
      let v_31 <- eval (concat (lshr v_13 v_7) v_30);
      let v_32 <- eval (concat (lshr v_12 v_7) v_31);
      let v_33 <- eval (concat (lshr v_11 v_7) v_32);
      let v_34 <- eval (concat (lshr v_10 v_7) v_33);
      let v_35 <- eval (concat (lshr v_9 v_7) v_34);
      let v_36 <- eval (concat (lshr v_8 v_7) v_35);
      let v_37 <- eval (concat (lshr v_6 v_7) v_36);
      setRegister (lhs.of_reg ymm_2) (mux (ugt v_4 (expression.bv_nat 64 15)) (expression.bv_nat 256 0) v_37);
      pure ()
     action
