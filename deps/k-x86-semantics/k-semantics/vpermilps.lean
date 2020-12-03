def vpermilps : instruction :=
  definst "vpermilps" $ do
    instr_pat $ fun (imm_0 : imm int) (mem_1 : Mem) (xmm_2 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_3 <- eval (handleImmediateWithSignExtend imm_0 8 8);
      let (v_4 : expression (bv 2)) <- eval (extract v_3 0 2);
      let v_5 <- evaluateAddress mem_1;
      let v_6 <- load v_5 16;
      let (v_7 : expression (bv 32)) <- eval (extract v_6 96 128);
      let (v_8 : expression (bv 32)) <- eval (extract v_6 64 96);
      let (v_9 : expression (bv 32)) <- eval (extract v_6 32 64);
      let (v_10 : expression (bv 32)) <- eval (extract v_6 0 32);
      let (v_11 : expression (bv 2)) <- eval (extract v_3 2 4);
      let (v_12 : expression (bv 2)) <- eval (extract v_3 4 6);
      let (v_13 : expression (bv 2)) <- eval (extract v_3 6 8);
      let v_14 <- eval (concat (mux (eq v_12 (expression.bv_nat 2 0)) v_7 (mux (eq v_12 (expression.bv_nat 2 1)) v_8 (mux (eq v_12 (expression.bv_nat 2 2)) v_9 v_10))) (mux (eq v_13 (expression.bv_nat 2 0)) v_7 (mux (eq v_13 (expression.bv_nat 2 1)) v_8 (mux (eq v_13 (expression.bv_nat 2 2)) v_9 v_10))));
      let v_15 <- eval (concat (mux (eq v_11 (expression.bv_nat 2 0)) v_7 (mux (eq v_11 (expression.bv_nat 2 1)) v_8 (mux (eq v_11 (expression.bv_nat 2 2)) v_9 v_10))) v_14);
      let v_16 <- eval (concat (mux (eq v_4 (expression.bv_nat 2 0)) v_7 (mux (eq v_4 (expression.bv_nat 2 1)) v_8 (mux (eq v_4 (expression.bv_nat 2 2)) v_9 v_10))) v_15);
      setRegister (lhs.of_reg xmm_2) v_16;
      pure ()
     action;
    instr_pat $ fun (imm_0 : imm int) (mem_1 : Mem) (ymm_2 : reg (bv 256)) =>
     let action : semantics Unit := do
      let v_3 <- eval (handleImmediateWithSignExtend imm_0 8 8);
      let (v_4 : expression (bv 2)) <- eval (extract v_3 0 2);
      let v_5 <- eval (eq v_4 (expression.bv_nat 2 0));
      let v_6 <- evaluateAddress mem_1;
      let v_7 <- load v_6 32;
      let (v_8 : expression (bv 32)) <- eval (extract v_7 96 128);
      let v_9 <- eval (eq v_4 (expression.bv_nat 2 1));
      let (v_10 : expression (bv 32)) <- eval (extract v_7 64 96);
      let v_11 <- eval (eq v_4 (expression.bv_nat 2 2));
      let (v_12 : expression (bv 32)) <- eval (extract v_7 32 64);
      let (v_13 : expression (bv 32)) <- eval (extract v_7 0 32);
      let (v_14 : expression (bv 2)) <- eval (extract v_3 2 4);
      let v_15 <- eval (eq v_14 (expression.bv_nat 2 0));
      let v_16 <- eval (eq v_14 (expression.bv_nat 2 1));
      let v_17 <- eval (eq v_14 (expression.bv_nat 2 2));
      let (v_18 : expression (bv 2)) <- eval (extract v_3 4 6);
      let v_19 <- eval (eq v_18 (expression.bv_nat 2 0));
      let v_20 <- eval (eq v_18 (expression.bv_nat 2 1));
      let v_21 <- eval (eq v_18 (expression.bv_nat 2 2));
      let (v_22 : expression (bv 2)) <- eval (extract v_3 6 8);
      let v_23 <- eval (eq v_22 (expression.bv_nat 2 0));
      let v_24 <- eval (eq v_22 (expression.bv_nat 2 1));
      let v_25 <- eval (eq v_22 (expression.bv_nat 2 2));
      let (v_26 : expression (bv 32)) <- eval (extract v_7 224 256);
      let (v_27 : expression (bv 32)) <- eval (extract v_7 192 224);
      let (v_28 : expression (bv 32)) <- eval (extract v_7 160 192);
      let (v_29 : expression (bv 32)) <- eval (extract v_7 128 160);
      let v_30 <- eval (concat (mux v_19 v_26 (mux v_20 v_27 (mux v_21 v_28 v_29))) (mux v_23 v_26 (mux v_24 v_27 (mux v_25 v_28 v_29))));
      let v_31 <- eval (concat (mux v_15 v_26 (mux v_16 v_27 (mux v_17 v_28 v_29))) v_30);
      let v_32 <- eval (concat (mux v_5 v_26 (mux v_9 v_27 (mux v_11 v_28 v_29))) v_31);
      let v_33 <- eval (concat (mux v_23 v_8 (mux v_24 v_10 (mux v_25 v_12 v_13))) v_32);
      let v_34 <- eval (concat (mux v_19 v_8 (mux v_20 v_10 (mux v_21 v_12 v_13))) v_33);
      let v_35 <- eval (concat (mux v_15 v_8 (mux v_16 v_10 (mux v_17 v_12 v_13))) v_34);
      let v_36 <- eval (concat (mux v_5 v_8 (mux v_9 v_10 (mux v_11 v_12 v_13))) v_35);
      setRegister (lhs.of_reg ymm_2) v_36;
      pure ()
     action;
    instr_pat $ fun (imm_0 : imm int) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_3 <- eval (handleImmediateWithSignExtend imm_0 8 8);
      let (v_4 : expression (bv 2)) <- eval (extract v_3 0 2);
      let v_5 <- getRegister (lhs.of_reg xmm_1);
      let (v_6 : expression (bv 32)) <- eval (extract v_5 96 128);
      let (v_7 : expression (bv 32)) <- eval (extract v_5 64 96);
      let (v_8 : expression (bv 32)) <- eval (extract v_5 32 64);
      let (v_9 : expression (bv 32)) <- eval (extract v_5 0 32);
      let (v_10 : expression (bv 2)) <- eval (extract v_3 2 4);
      let (v_11 : expression (bv 2)) <- eval (extract v_3 4 6);
      let (v_12 : expression (bv 2)) <- eval (extract v_3 6 8);
      let v_13 <- eval (concat (mux (eq v_11 (expression.bv_nat 2 0)) v_6 (mux (eq v_11 (expression.bv_nat 2 1)) v_7 (mux (eq v_11 (expression.bv_nat 2 2)) v_8 v_9))) (mux (eq v_12 (expression.bv_nat 2 0)) v_6 (mux (eq v_12 (expression.bv_nat 2 1)) v_7 (mux (eq v_12 (expression.bv_nat 2 2)) v_8 v_9))));
      let v_14 <- eval (concat (mux (eq v_10 (expression.bv_nat 2 0)) v_6 (mux (eq v_10 (expression.bv_nat 2 1)) v_7 (mux (eq v_10 (expression.bv_nat 2 2)) v_8 v_9))) v_13);
      let v_15 <- eval (concat (mux (eq v_4 (expression.bv_nat 2 0)) v_6 (mux (eq v_4 (expression.bv_nat 2 1)) v_7 (mux (eq v_4 (expression.bv_nat 2 2)) v_8 v_9))) v_14);
      setRegister (lhs.of_reg xmm_2) v_15;
      pure ()
     action;
    instr_pat $ fun (imm_0 : imm int) (ymm_1 : reg (bv 256)) (ymm_2 : reg (bv 256)) =>
     let action : semantics Unit := do
      let v_3 <- eval (handleImmediateWithSignExtend imm_0 8 8);
      let (v_4 : expression (bv 2)) <- eval (extract v_3 0 2);
      let v_5 <- eval (eq v_4 (expression.bv_nat 2 0));
      let v_6 <- getRegister (lhs.of_reg ymm_1);
      let (v_7 : expression (bv 32)) <- eval (extract v_6 96 128);
      let v_8 <- eval (eq v_4 (expression.bv_nat 2 1));
      let (v_9 : expression (bv 32)) <- eval (extract v_6 64 96);
      let v_10 <- eval (eq v_4 (expression.bv_nat 2 2));
      let (v_11 : expression (bv 32)) <- eval (extract v_6 32 64);
      let (v_12 : expression (bv 32)) <- eval (extract v_6 0 32);
      let (v_13 : expression (bv 2)) <- eval (extract v_3 2 4);
      let v_14 <- eval (eq v_13 (expression.bv_nat 2 0));
      let v_15 <- eval (eq v_13 (expression.bv_nat 2 1));
      let v_16 <- eval (eq v_13 (expression.bv_nat 2 2));
      let (v_17 : expression (bv 2)) <- eval (extract v_3 4 6);
      let v_18 <- eval (eq v_17 (expression.bv_nat 2 0));
      let v_19 <- eval (eq v_17 (expression.bv_nat 2 1));
      let v_20 <- eval (eq v_17 (expression.bv_nat 2 2));
      let (v_21 : expression (bv 2)) <- eval (extract v_3 6 8);
      let v_22 <- eval (eq v_21 (expression.bv_nat 2 0));
      let v_23 <- eval (eq v_21 (expression.bv_nat 2 1));
      let v_24 <- eval (eq v_21 (expression.bv_nat 2 2));
      let (v_25 : expression (bv 32)) <- eval (extract v_6 224 256);
      let (v_26 : expression (bv 32)) <- eval (extract v_6 192 224);
      let (v_27 : expression (bv 32)) <- eval (extract v_6 160 192);
      let (v_28 : expression (bv 32)) <- eval (extract v_6 128 160);
      let v_29 <- eval (concat (mux v_18 v_25 (mux v_19 v_26 (mux v_20 v_27 v_28))) (mux v_22 v_25 (mux v_23 v_26 (mux v_24 v_27 v_28))));
      let v_30 <- eval (concat (mux v_14 v_25 (mux v_15 v_26 (mux v_16 v_27 v_28))) v_29);
      let v_31 <- eval (concat (mux v_5 v_25 (mux v_8 v_26 (mux v_10 v_27 v_28))) v_30);
      let v_32 <- eval (concat (mux v_22 v_7 (mux v_23 v_9 (mux v_24 v_11 v_12))) v_31);
      let v_33 <- eval (concat (mux v_18 v_7 (mux v_19 v_9 (mux v_20 v_11 v_12))) v_32);
      let v_34 <- eval (concat (mux v_14 v_7 (mux v_15 v_9 (mux v_16 v_11 v_12))) v_33);
      let v_35 <- eval (concat (mux v_5 v_7 (mux v_8 v_9 (mux v_10 v_11 v_12))) v_34);
      setRegister (lhs.of_reg ymm_2) v_35;
      pure ()
     action;
    instr_pat $ fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_3 <- evaluateAddress mem_0;
      let v_4 <- load v_3 16;
      let (v_5 : expression (bv 2)) <- eval (extract v_4 30 32);
      let v_6 <- getRegister (lhs.of_reg xmm_1);
      let (v_7 : expression (bv 32)) <- eval (extract v_6 96 128);
      let (v_8 : expression (bv 32)) <- eval (extract v_6 64 96);
      let (v_9 : expression (bv 32)) <- eval (extract v_6 32 64);
      let (v_10 : expression (bv 32)) <- eval (extract v_6 0 32);
      let (v_11 : expression (bv 2)) <- eval (extract v_4 62 64);
      let (v_12 : expression (bv 2)) <- eval (extract v_4 94 96);
      let (v_13 : expression (bv 2)) <- eval (extract v_4 126 128);
      let v_14 <- eval (concat (mux (eq v_12 (expression.bv_nat 2 0)) v_7 (mux (eq v_12 (expression.bv_nat 2 1)) v_8 (mux (eq v_12 (expression.bv_nat 2 2)) v_9 v_10))) (mux (eq v_13 (expression.bv_nat 2 0)) v_7 (mux (eq v_13 (expression.bv_nat 2 1)) v_8 (mux (eq v_13 (expression.bv_nat 2 2)) v_9 v_10))));
      let v_15 <- eval (concat (mux (eq v_11 (expression.bv_nat 2 0)) v_7 (mux (eq v_11 (expression.bv_nat 2 1)) v_8 (mux (eq v_11 (expression.bv_nat 2 2)) v_9 v_10))) v_14);
      let v_16 <- eval (concat (mux (eq v_5 (expression.bv_nat 2 0)) v_7 (mux (eq v_5 (expression.bv_nat 2 1)) v_8 (mux (eq v_5 (expression.bv_nat 2 2)) v_9 v_10))) v_15);
      setRegister (lhs.of_reg xmm_2) v_16;
      pure ()
     action;
    instr_pat $ fun (mem_0 : Mem) (ymm_1 : reg (bv 256)) (ymm_2 : reg (bv 256)) =>
     let action : semantics Unit := do
      let v_3 <- evaluateAddress mem_0;
      let v_4 <- load v_3 32;
      let (v_5 : expression (bv 2)) <- eval (extract v_4 30 32);
      let v_6 <- getRegister (lhs.of_reg ymm_1);
      let (v_7 : expression (bv 32)) <- eval (extract v_6 96 128);
      let (v_8 : expression (bv 32)) <- eval (extract v_6 64 96);
      let (v_9 : expression (bv 32)) <- eval (extract v_6 32 64);
      let (v_10 : expression (bv 32)) <- eval (extract v_6 0 32);
      let (v_11 : expression (bv 2)) <- eval (extract v_4 62 64);
      let (v_12 : expression (bv 2)) <- eval (extract v_4 94 96);
      let (v_13 : expression (bv 2)) <- eval (extract v_4 126 128);
      let (v_14 : expression (bv 2)) <- eval (extract v_4 158 160);
      let (v_15 : expression (bv 32)) <- eval (extract v_6 224 256);
      let (v_16 : expression (bv 32)) <- eval (extract v_6 192 224);
      let (v_17 : expression (bv 32)) <- eval (extract v_6 160 192);
      let (v_18 : expression (bv 32)) <- eval (extract v_6 128 160);
      let (v_19 : expression (bv 2)) <- eval (extract v_4 190 192);
      let (v_20 : expression (bv 2)) <- eval (extract v_4 222 224);
      let (v_21 : expression (bv 2)) <- eval (extract v_4 254 256);
      let v_22 <- eval (concat (mux (eq v_20 (expression.bv_nat 2 0)) v_15 (mux (eq v_20 (expression.bv_nat 2 1)) v_16 (mux (eq v_20 (expression.bv_nat 2 2)) v_17 v_18))) (mux (eq v_21 (expression.bv_nat 2 0)) v_15 (mux (eq v_21 (expression.bv_nat 2 1)) v_16 (mux (eq v_21 (expression.bv_nat 2 2)) v_17 v_18))));
      let v_23 <- eval (concat (mux (eq v_19 (expression.bv_nat 2 0)) v_15 (mux (eq v_19 (expression.bv_nat 2 1)) v_16 (mux (eq v_19 (expression.bv_nat 2 2)) v_17 v_18))) v_22);
      let v_24 <- eval (concat (mux (eq v_14 (expression.bv_nat 2 0)) v_15 (mux (eq v_14 (expression.bv_nat 2 1)) v_16 (mux (eq v_14 (expression.bv_nat 2 2)) v_17 v_18))) v_23);
      let v_25 <- eval (concat (mux (eq v_13 (expression.bv_nat 2 0)) v_7 (mux (eq v_13 (expression.bv_nat 2 1)) v_8 (mux (eq v_13 (expression.bv_nat 2 2)) v_9 v_10))) v_24);
      let v_26 <- eval (concat (mux (eq v_12 (expression.bv_nat 2 0)) v_7 (mux (eq v_12 (expression.bv_nat 2 1)) v_8 (mux (eq v_12 (expression.bv_nat 2 2)) v_9 v_10))) v_25);
      let v_27 <- eval (concat (mux (eq v_11 (expression.bv_nat 2 0)) v_7 (mux (eq v_11 (expression.bv_nat 2 1)) v_8 (mux (eq v_11 (expression.bv_nat 2 2)) v_9 v_10))) v_26);
      let v_28 <- eval (concat (mux (eq v_5 (expression.bv_nat 2 0)) v_7 (mux (eq v_5 (expression.bv_nat 2 1)) v_8 (mux (eq v_5 (expression.bv_nat 2 2)) v_9 v_10))) v_27);
      setRegister (lhs.of_reg ymm_2) v_28;
      pure ()
     action;
    instr_pat $ fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_3 <- getRegister (lhs.of_reg xmm_0);
      let (v_4 : expression (bv 2)) <- eval (extract v_3 30 32);
      let v_5 <- getRegister (lhs.of_reg xmm_1);
      let (v_6 : expression (bv 32)) <- eval (extract v_5 96 128);
      let (v_7 : expression (bv 32)) <- eval (extract v_5 64 96);
      let (v_8 : expression (bv 32)) <- eval (extract v_5 32 64);
      let (v_9 : expression (bv 32)) <- eval (extract v_5 0 32);
      let (v_10 : expression (bv 2)) <- eval (extract v_3 62 64);
      let (v_11 : expression (bv 2)) <- eval (extract v_3 94 96);
      let (v_12 : expression (bv 2)) <- eval (extract v_3 126 128);
      let v_13 <- eval (concat (mux (eq v_11 (expression.bv_nat 2 0)) v_6 (mux (eq v_11 (expression.bv_nat 2 1)) v_7 (mux (eq v_11 (expression.bv_nat 2 2)) v_8 v_9))) (mux (eq v_12 (expression.bv_nat 2 0)) v_6 (mux (eq v_12 (expression.bv_nat 2 1)) v_7 (mux (eq v_12 (expression.bv_nat 2 2)) v_8 v_9))));
      let v_14 <- eval (concat (mux (eq v_10 (expression.bv_nat 2 0)) v_6 (mux (eq v_10 (expression.bv_nat 2 1)) v_7 (mux (eq v_10 (expression.bv_nat 2 2)) v_8 v_9))) v_13);
      let v_15 <- eval (concat (mux (eq v_4 (expression.bv_nat 2 0)) v_6 (mux (eq v_4 (expression.bv_nat 2 1)) v_7 (mux (eq v_4 (expression.bv_nat 2 2)) v_8 v_9))) v_14);
      setRegister (lhs.of_reg xmm_2) v_15;
      pure ()
     action;
    instr_pat $ fun (ymm_0 : reg (bv 256)) (ymm_1 : reg (bv 256)) (ymm_2 : reg (bv 256)) =>
     let action : semantics Unit := do
      let v_3 <- getRegister (lhs.of_reg ymm_0);
      let (v_4 : expression (bv 2)) <- eval (extract v_3 30 32);
      let v_5 <- getRegister (lhs.of_reg ymm_1);
      let (v_6 : expression (bv 32)) <- eval (extract v_5 96 128);
      let (v_7 : expression (bv 32)) <- eval (extract v_5 64 96);
      let (v_8 : expression (bv 32)) <- eval (extract v_5 32 64);
      let (v_9 : expression (bv 32)) <- eval (extract v_5 0 32);
      let (v_10 : expression (bv 2)) <- eval (extract v_3 62 64);
      let (v_11 : expression (bv 2)) <- eval (extract v_3 94 96);
      let (v_12 : expression (bv 2)) <- eval (extract v_3 126 128);
      let (v_13 : expression (bv 2)) <- eval (extract v_3 158 160);
      let (v_14 : expression (bv 32)) <- eval (extract v_5 224 256);
      let (v_15 : expression (bv 32)) <- eval (extract v_5 192 224);
      let (v_16 : expression (bv 32)) <- eval (extract v_5 160 192);
      let (v_17 : expression (bv 32)) <- eval (extract v_5 128 160);
      let (v_18 : expression (bv 2)) <- eval (extract v_3 190 192);
      let (v_19 : expression (bv 2)) <- eval (extract v_3 222 224);
      let (v_20 : expression (bv 2)) <- eval (extract v_3 254 256);
      let v_21 <- eval (concat (mux (eq v_19 (expression.bv_nat 2 0)) v_14 (mux (eq v_19 (expression.bv_nat 2 1)) v_15 (mux (eq v_19 (expression.bv_nat 2 2)) v_16 v_17))) (mux (eq v_20 (expression.bv_nat 2 0)) v_14 (mux (eq v_20 (expression.bv_nat 2 1)) v_15 (mux (eq v_20 (expression.bv_nat 2 2)) v_16 v_17))));
      let v_22 <- eval (concat (mux (eq v_18 (expression.bv_nat 2 0)) v_14 (mux (eq v_18 (expression.bv_nat 2 1)) v_15 (mux (eq v_18 (expression.bv_nat 2 2)) v_16 v_17))) v_21);
      let v_23 <- eval (concat (mux (eq v_13 (expression.bv_nat 2 0)) v_14 (mux (eq v_13 (expression.bv_nat 2 1)) v_15 (mux (eq v_13 (expression.bv_nat 2 2)) v_16 v_17))) v_22);
      let v_24 <- eval (concat (mux (eq v_12 (expression.bv_nat 2 0)) v_6 (mux (eq v_12 (expression.bv_nat 2 1)) v_7 (mux (eq v_12 (expression.bv_nat 2 2)) v_8 v_9))) v_23);
      let v_25 <- eval (concat (mux (eq v_11 (expression.bv_nat 2 0)) v_6 (mux (eq v_11 (expression.bv_nat 2 1)) v_7 (mux (eq v_11 (expression.bv_nat 2 2)) v_8 v_9))) v_24);
      let v_26 <- eval (concat (mux (eq v_10 (expression.bv_nat 2 0)) v_6 (mux (eq v_10 (expression.bv_nat 2 1)) v_7 (mux (eq v_10 (expression.bv_nat 2 2)) v_8 v_9))) v_25);
      let v_27 <- eval (concat (mux (eq v_4 (expression.bv_nat 2 0)) v_6 (mux (eq v_4 (expression.bv_nat 2 1)) v_7 (mux (eq v_4 (expression.bv_nat 2 2)) v_8 v_9))) v_26);
      setRegister (lhs.of_reg ymm_2) v_27;
      pure ()
     action
