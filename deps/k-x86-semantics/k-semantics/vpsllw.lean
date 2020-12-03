def vpsllw : instruction :=
  definst "vpsllw" $ do
    instr_pat $ fun (imm_0 : imm int) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_3 <- eval (handleImmediateWithSignExtend imm_0 8 8);
      let v_4 <- eval (concat (expression.bv_nat 56 0) v_3);
      let v_5 <- getRegister (lhs.of_reg xmm_1);
      let (v_6 : expression (bv 16)) <- eval (extract v_5 0 16);
      let v_7 <- eval (concat (expression.bv_nat 8 0) v_3);
      let (v_8 : expression (bv 16)) <- eval (extract (shl v_6 v_7) 0 16);
      let (v_9 : expression (bv 16)) <- eval (extract v_5 16 32);
      let (v_10 : expression (bv 16)) <- eval (extract (shl v_9 v_7) 0 16);
      let (v_11 : expression (bv 16)) <- eval (extract v_5 32 48);
      let (v_12 : expression (bv 16)) <- eval (extract (shl v_11 v_7) 0 16);
      let (v_13 : expression (bv 16)) <- eval (extract v_5 48 64);
      let (v_14 : expression (bv 16)) <- eval (extract (shl v_13 v_7) 0 16);
      let (v_15 : expression (bv 16)) <- eval (extract v_5 64 80);
      let (v_16 : expression (bv 16)) <- eval (extract (shl v_15 v_7) 0 16);
      let (v_17 : expression (bv 16)) <- eval (extract v_5 80 96);
      let (v_18 : expression (bv 16)) <- eval (extract (shl v_17 v_7) 0 16);
      let (v_19 : expression (bv 16)) <- eval (extract v_5 96 112);
      let (v_20 : expression (bv 16)) <- eval (extract (shl v_19 v_7) 0 16);
      let (v_21 : expression (bv 16)) <- eval (extract v_5 112 128);
      let (v_22 : expression (bv 16)) <- eval (extract (shl v_21 v_7) 0 16);
      let v_23 <- eval (concat v_20 v_22);
      let v_24 <- eval (concat v_18 v_23);
      let v_25 <- eval (concat v_16 v_24);
      let v_26 <- eval (concat v_14 v_25);
      let v_27 <- eval (concat v_12 v_26);
      let v_28 <- eval (concat v_10 v_27);
      let v_29 <- eval (concat v_8 v_28);
      setRegister (lhs.of_reg xmm_2) (mux (ugt v_4 (expression.bv_nat 64 15)) (expression.bv_nat 128 0) v_29);
      pure ()
     action;
    instr_pat $ fun (imm_0 : imm int) (ymm_1 : reg (bv 256)) (ymm_2 : reg (bv 256)) =>
     let action : semantics Unit := do
      let v_3 <- eval (handleImmediateWithSignExtend imm_0 8 8);
      let v_4 <- eval (concat (expression.bv_nat 56 0) v_3);
      let v_5 <- getRegister (lhs.of_reg ymm_1);
      let (v_6 : expression (bv 16)) <- eval (extract v_5 0 16);
      let v_7 <- eval (concat (expression.bv_nat 8 0) v_3);
      let (v_8 : expression (bv 16)) <- eval (extract (shl v_6 v_7) 0 16);
      let (v_9 : expression (bv 16)) <- eval (extract v_5 16 32);
      let (v_10 : expression (bv 16)) <- eval (extract (shl v_9 v_7) 0 16);
      let (v_11 : expression (bv 16)) <- eval (extract v_5 32 48);
      let (v_12 : expression (bv 16)) <- eval (extract (shl v_11 v_7) 0 16);
      let (v_13 : expression (bv 16)) <- eval (extract v_5 48 64);
      let (v_14 : expression (bv 16)) <- eval (extract (shl v_13 v_7) 0 16);
      let (v_15 : expression (bv 16)) <- eval (extract v_5 64 80);
      let (v_16 : expression (bv 16)) <- eval (extract (shl v_15 v_7) 0 16);
      let (v_17 : expression (bv 16)) <- eval (extract v_5 80 96);
      let (v_18 : expression (bv 16)) <- eval (extract (shl v_17 v_7) 0 16);
      let (v_19 : expression (bv 16)) <- eval (extract v_5 96 112);
      let (v_20 : expression (bv 16)) <- eval (extract (shl v_19 v_7) 0 16);
      let (v_21 : expression (bv 16)) <- eval (extract v_5 112 128);
      let (v_22 : expression (bv 16)) <- eval (extract (shl v_21 v_7) 0 16);
      let (v_23 : expression (bv 16)) <- eval (extract v_5 128 144);
      let (v_24 : expression (bv 16)) <- eval (extract (shl v_23 v_7) 0 16);
      let (v_25 : expression (bv 16)) <- eval (extract v_5 144 160);
      let (v_26 : expression (bv 16)) <- eval (extract (shl v_25 v_7) 0 16);
      let (v_27 : expression (bv 16)) <- eval (extract v_5 160 176);
      let (v_28 : expression (bv 16)) <- eval (extract (shl v_27 v_7) 0 16);
      let (v_29 : expression (bv 16)) <- eval (extract v_5 176 192);
      let (v_30 : expression (bv 16)) <- eval (extract (shl v_29 v_7) 0 16);
      let (v_31 : expression (bv 16)) <- eval (extract v_5 192 208);
      let (v_32 : expression (bv 16)) <- eval (extract (shl v_31 v_7) 0 16);
      let (v_33 : expression (bv 16)) <- eval (extract v_5 208 224);
      let (v_34 : expression (bv 16)) <- eval (extract (shl v_33 v_7) 0 16);
      let (v_35 : expression (bv 16)) <- eval (extract v_5 224 240);
      let (v_36 : expression (bv 16)) <- eval (extract (shl v_35 v_7) 0 16);
      let (v_37 : expression (bv 16)) <- eval (extract v_5 240 256);
      let (v_38 : expression (bv 16)) <- eval (extract (shl v_37 v_7) 0 16);
      let v_39 <- eval (concat v_36 v_38);
      let v_40 <- eval (concat v_34 v_39);
      let v_41 <- eval (concat v_32 v_40);
      let v_42 <- eval (concat v_30 v_41);
      let v_43 <- eval (concat v_28 v_42);
      let v_44 <- eval (concat v_26 v_43);
      let v_45 <- eval (concat v_24 v_44);
      let v_46 <- eval (concat v_22 v_45);
      let v_47 <- eval (concat v_20 v_46);
      let v_48 <- eval (concat v_18 v_47);
      let v_49 <- eval (concat v_16 v_48);
      let v_50 <- eval (concat v_14 v_49);
      let v_51 <- eval (concat v_12 v_50);
      let v_52 <- eval (concat v_10 v_51);
      let v_53 <- eval (concat v_8 v_52);
      setRegister (lhs.of_reg ymm_2) (mux (ugt v_4 (expression.bv_nat 64 15)) (expression.bv_nat 256 0) v_53);
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
      let (v_9 : expression (bv 16)) <- eval (extract (shl v_7 v_8) 0 16);
      let (v_10 : expression (bv 16)) <- eval (extract v_6 16 32);
      let (v_11 : expression (bv 16)) <- eval (extract (shl v_10 v_8) 0 16);
      let (v_12 : expression (bv 16)) <- eval (extract v_6 32 48);
      let (v_13 : expression (bv 16)) <- eval (extract (shl v_12 v_8) 0 16);
      let (v_14 : expression (bv 16)) <- eval (extract v_6 48 64);
      let (v_15 : expression (bv 16)) <- eval (extract (shl v_14 v_8) 0 16);
      let (v_16 : expression (bv 16)) <- eval (extract v_6 64 80);
      let (v_17 : expression (bv 16)) <- eval (extract (shl v_16 v_8) 0 16);
      let (v_18 : expression (bv 16)) <- eval (extract v_6 80 96);
      let (v_19 : expression (bv 16)) <- eval (extract (shl v_18 v_8) 0 16);
      let (v_20 : expression (bv 16)) <- eval (extract v_6 96 112);
      let (v_21 : expression (bv 16)) <- eval (extract (shl v_20 v_8) 0 16);
      let (v_22 : expression (bv 16)) <- eval (extract v_6 112 128);
      let (v_23 : expression (bv 16)) <- eval (extract (shl v_22 v_8) 0 16);
      let v_24 <- eval (concat v_21 v_23);
      let v_25 <- eval (concat v_19 v_24);
      let v_26 <- eval (concat v_17 v_25);
      let v_27 <- eval (concat v_15 v_26);
      let v_28 <- eval (concat v_13 v_27);
      let v_29 <- eval (concat v_11 v_28);
      let v_30 <- eval (concat v_9 v_29);
      setRegister (lhs.of_reg xmm_2) (mux (ugt v_5 (expression.bv_nat 64 15)) (expression.bv_nat 128 0) v_30);
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
      let (v_9 : expression (bv 16)) <- eval (extract (shl v_7 v_8) 0 16);
      let (v_10 : expression (bv 16)) <- eval (extract v_6 16 32);
      let (v_11 : expression (bv 16)) <- eval (extract (shl v_10 v_8) 0 16);
      let (v_12 : expression (bv 16)) <- eval (extract v_6 32 48);
      let (v_13 : expression (bv 16)) <- eval (extract (shl v_12 v_8) 0 16);
      let (v_14 : expression (bv 16)) <- eval (extract v_6 48 64);
      let (v_15 : expression (bv 16)) <- eval (extract (shl v_14 v_8) 0 16);
      let (v_16 : expression (bv 16)) <- eval (extract v_6 64 80);
      let (v_17 : expression (bv 16)) <- eval (extract (shl v_16 v_8) 0 16);
      let (v_18 : expression (bv 16)) <- eval (extract v_6 80 96);
      let (v_19 : expression (bv 16)) <- eval (extract (shl v_18 v_8) 0 16);
      let (v_20 : expression (bv 16)) <- eval (extract v_6 96 112);
      let (v_21 : expression (bv 16)) <- eval (extract (shl v_20 v_8) 0 16);
      let (v_22 : expression (bv 16)) <- eval (extract v_6 112 128);
      let (v_23 : expression (bv 16)) <- eval (extract (shl v_22 v_8) 0 16);
      let (v_24 : expression (bv 16)) <- eval (extract v_6 128 144);
      let (v_25 : expression (bv 16)) <- eval (extract (shl v_24 v_8) 0 16);
      let (v_26 : expression (bv 16)) <- eval (extract v_6 144 160);
      let (v_27 : expression (bv 16)) <- eval (extract (shl v_26 v_8) 0 16);
      let (v_28 : expression (bv 16)) <- eval (extract v_6 160 176);
      let (v_29 : expression (bv 16)) <- eval (extract (shl v_28 v_8) 0 16);
      let (v_30 : expression (bv 16)) <- eval (extract v_6 176 192);
      let (v_31 : expression (bv 16)) <- eval (extract (shl v_30 v_8) 0 16);
      let (v_32 : expression (bv 16)) <- eval (extract v_6 192 208);
      let (v_33 : expression (bv 16)) <- eval (extract (shl v_32 v_8) 0 16);
      let (v_34 : expression (bv 16)) <- eval (extract v_6 208 224);
      let (v_35 : expression (bv 16)) <- eval (extract (shl v_34 v_8) 0 16);
      let (v_36 : expression (bv 16)) <- eval (extract v_6 224 240);
      let (v_37 : expression (bv 16)) <- eval (extract (shl v_36 v_8) 0 16);
      let (v_38 : expression (bv 16)) <- eval (extract v_6 240 256);
      let (v_39 : expression (bv 16)) <- eval (extract (shl v_38 v_8) 0 16);
      let v_40 <- eval (concat v_37 v_39);
      let v_41 <- eval (concat v_35 v_40);
      let v_42 <- eval (concat v_33 v_41);
      let v_43 <- eval (concat v_31 v_42);
      let v_44 <- eval (concat v_29 v_43);
      let v_45 <- eval (concat v_27 v_44);
      let v_46 <- eval (concat v_25 v_45);
      let v_47 <- eval (concat v_23 v_46);
      let v_48 <- eval (concat v_21 v_47);
      let v_49 <- eval (concat v_19 v_48);
      let v_50 <- eval (concat v_17 v_49);
      let v_51 <- eval (concat v_15 v_50);
      let v_52 <- eval (concat v_13 v_51);
      let v_53 <- eval (concat v_11 v_52);
      let v_54 <- eval (concat v_9 v_53);
      setRegister (lhs.of_reg ymm_2) (mux (ugt v_5 (expression.bv_nat 64 15)) (expression.bv_nat 256 0) v_54);
      pure ()
     action;
    instr_pat $ fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_3 <- getRegister (lhs.of_reg xmm_0);
      let (v_4 : expression (bv 64)) <- eval (extract v_3 64 128);
      let v_5 <- getRegister (lhs.of_reg xmm_1);
      let (v_6 : expression (bv 16)) <- eval (extract v_5 0 16);
      let (v_7 : expression (bv 16)) <- eval (extract v_3 112 128);
      let (v_8 : expression (bv 16)) <- eval (extract (shl v_6 v_7) 0 16);
      let (v_9 : expression (bv 16)) <- eval (extract v_5 16 32);
      let (v_10 : expression (bv 16)) <- eval (extract (shl v_9 v_7) 0 16);
      let (v_11 : expression (bv 16)) <- eval (extract v_5 32 48);
      let (v_12 : expression (bv 16)) <- eval (extract (shl v_11 v_7) 0 16);
      let (v_13 : expression (bv 16)) <- eval (extract v_5 48 64);
      let (v_14 : expression (bv 16)) <- eval (extract (shl v_13 v_7) 0 16);
      let (v_15 : expression (bv 16)) <- eval (extract v_5 64 80);
      let (v_16 : expression (bv 16)) <- eval (extract (shl v_15 v_7) 0 16);
      let (v_17 : expression (bv 16)) <- eval (extract v_5 80 96);
      let (v_18 : expression (bv 16)) <- eval (extract (shl v_17 v_7) 0 16);
      let (v_19 : expression (bv 16)) <- eval (extract v_5 96 112);
      let (v_20 : expression (bv 16)) <- eval (extract (shl v_19 v_7) 0 16);
      let (v_21 : expression (bv 16)) <- eval (extract v_5 112 128);
      let (v_22 : expression (bv 16)) <- eval (extract (shl v_21 v_7) 0 16);
      let v_23 <- eval (concat v_20 v_22);
      let v_24 <- eval (concat v_18 v_23);
      let v_25 <- eval (concat v_16 v_24);
      let v_26 <- eval (concat v_14 v_25);
      let v_27 <- eval (concat v_12 v_26);
      let v_28 <- eval (concat v_10 v_27);
      let v_29 <- eval (concat v_8 v_28);
      setRegister (lhs.of_reg xmm_2) (mux (ugt v_4 (expression.bv_nat 64 15)) (expression.bv_nat 128 0) v_29);
      pure ()
     action;
    instr_pat $ fun (xmm_0 : reg (bv 128)) (ymm_1 : reg (bv 256)) (ymm_2 : reg (bv 256)) =>
     let action : semantics Unit := do
      let v_3 <- getRegister (lhs.of_reg xmm_0);
      let (v_4 : expression (bv 64)) <- eval (extract v_3 64 128);
      let v_5 <- getRegister (lhs.of_reg ymm_1);
      let (v_6 : expression (bv 16)) <- eval (extract v_5 0 16);
      let (v_7 : expression (bv 16)) <- eval (extract v_3 112 128);
      let (v_8 : expression (bv 16)) <- eval (extract (shl v_6 v_7) 0 16);
      let (v_9 : expression (bv 16)) <- eval (extract v_5 16 32);
      let (v_10 : expression (bv 16)) <- eval (extract (shl v_9 v_7) 0 16);
      let (v_11 : expression (bv 16)) <- eval (extract v_5 32 48);
      let (v_12 : expression (bv 16)) <- eval (extract (shl v_11 v_7) 0 16);
      let (v_13 : expression (bv 16)) <- eval (extract v_5 48 64);
      let (v_14 : expression (bv 16)) <- eval (extract (shl v_13 v_7) 0 16);
      let (v_15 : expression (bv 16)) <- eval (extract v_5 64 80);
      let (v_16 : expression (bv 16)) <- eval (extract (shl v_15 v_7) 0 16);
      let (v_17 : expression (bv 16)) <- eval (extract v_5 80 96);
      let (v_18 : expression (bv 16)) <- eval (extract (shl v_17 v_7) 0 16);
      let (v_19 : expression (bv 16)) <- eval (extract v_5 96 112);
      let (v_20 : expression (bv 16)) <- eval (extract (shl v_19 v_7) 0 16);
      let (v_21 : expression (bv 16)) <- eval (extract v_5 112 128);
      let (v_22 : expression (bv 16)) <- eval (extract (shl v_21 v_7) 0 16);
      let (v_23 : expression (bv 16)) <- eval (extract v_5 128 144);
      let (v_24 : expression (bv 16)) <- eval (extract (shl v_23 v_7) 0 16);
      let (v_25 : expression (bv 16)) <- eval (extract v_5 144 160);
      let (v_26 : expression (bv 16)) <- eval (extract (shl v_25 v_7) 0 16);
      let (v_27 : expression (bv 16)) <- eval (extract v_5 160 176);
      let (v_28 : expression (bv 16)) <- eval (extract (shl v_27 v_7) 0 16);
      let (v_29 : expression (bv 16)) <- eval (extract v_5 176 192);
      let (v_30 : expression (bv 16)) <- eval (extract (shl v_29 v_7) 0 16);
      let (v_31 : expression (bv 16)) <- eval (extract v_5 192 208);
      let (v_32 : expression (bv 16)) <- eval (extract (shl v_31 v_7) 0 16);
      let (v_33 : expression (bv 16)) <- eval (extract v_5 208 224);
      let (v_34 : expression (bv 16)) <- eval (extract (shl v_33 v_7) 0 16);
      let (v_35 : expression (bv 16)) <- eval (extract v_5 224 240);
      let (v_36 : expression (bv 16)) <- eval (extract (shl v_35 v_7) 0 16);
      let (v_37 : expression (bv 16)) <- eval (extract v_5 240 256);
      let (v_38 : expression (bv 16)) <- eval (extract (shl v_37 v_7) 0 16);
      let v_39 <- eval (concat v_36 v_38);
      let v_40 <- eval (concat v_34 v_39);
      let v_41 <- eval (concat v_32 v_40);
      let v_42 <- eval (concat v_30 v_41);
      let v_43 <- eval (concat v_28 v_42);
      let v_44 <- eval (concat v_26 v_43);
      let v_45 <- eval (concat v_24 v_44);
      let v_46 <- eval (concat v_22 v_45);
      let v_47 <- eval (concat v_20 v_46);
      let v_48 <- eval (concat v_18 v_47);
      let v_49 <- eval (concat v_16 v_48);
      let v_50 <- eval (concat v_14 v_49);
      let v_51 <- eval (concat v_12 v_50);
      let v_52 <- eval (concat v_10 v_51);
      let v_53 <- eval (concat v_8 v_52);
      setRegister (lhs.of_reg ymm_2) (mux (ugt v_4 (expression.bv_nat 64 15)) (expression.bv_nat 256 0) v_53);
      pure ()
     action
