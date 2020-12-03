def vpunpcklwd : instruction :=
  definst "vpunpcklwd" $ do
    instr_pat $ fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_3 <- evaluateAddress mem_0;
      let v_4 <- load v_3 16;
      let (v_5 : expression (bv 16)) <- eval (extract v_4 64 80);
      let v_6 <- getRegister (lhs.of_reg xmm_1);
      let (v_7 : expression (bv 16)) <- eval (extract v_6 64 80);
      let v_8 <- eval (concat v_5 v_7);
      let (v_9 : expression (bv 16)) <- eval (extract v_4 80 96);
      let (v_10 : expression (bv 16)) <- eval (extract v_6 80 96);
      let v_11 <- eval (concat v_9 v_10);
      let (v_12 : expression (bv 16)) <- eval (extract v_4 96 112);
      let (v_13 : expression (bv 16)) <- eval (extract v_6 96 112);
      let v_14 <- eval (concat v_12 v_13);
      let (v_15 : expression (bv 16)) <- eval (extract v_4 112 128);
      let (v_16 : expression (bv 16)) <- eval (extract v_6 112 128);
      let v_17 <- eval (concat v_15 v_16);
      let v_18 <- eval (concat v_14 v_17);
      let v_19 <- eval (concat v_11 v_18);
      let v_20 <- eval (concat v_8 v_19);
      setRegister (lhs.of_reg xmm_2) v_20;
      pure ()
     action;
    instr_pat $ fun (mem_0 : Mem) (ymm_1 : reg (bv 256)) (ymm_2 : reg (bv 256)) =>
     let action : semantics Unit := do
      let v_3 <- evaluateAddress mem_0;
      let v_4 <- load v_3 32;
      let (v_5 : expression (bv 16)) <- eval (extract v_4 64 80);
      let v_6 <- getRegister (lhs.of_reg ymm_1);
      let (v_7 : expression (bv 16)) <- eval (extract v_6 64 80);
      let v_8 <- eval (concat v_5 v_7);
      let (v_9 : expression (bv 16)) <- eval (extract v_4 80 96);
      let (v_10 : expression (bv 16)) <- eval (extract v_6 80 96);
      let v_11 <- eval (concat v_9 v_10);
      let (v_12 : expression (bv 16)) <- eval (extract v_4 96 112);
      let (v_13 : expression (bv 16)) <- eval (extract v_6 96 112);
      let v_14 <- eval (concat v_12 v_13);
      let (v_15 : expression (bv 16)) <- eval (extract v_4 112 128);
      let (v_16 : expression (bv 16)) <- eval (extract v_6 112 128);
      let v_17 <- eval (concat v_15 v_16);
      let (v_18 : expression (bv 16)) <- eval (extract v_4 192 208);
      let (v_19 : expression (bv 16)) <- eval (extract v_6 192 208);
      let v_20 <- eval (concat v_18 v_19);
      let (v_21 : expression (bv 16)) <- eval (extract v_4 208 224);
      let (v_22 : expression (bv 16)) <- eval (extract v_6 208 224);
      let v_23 <- eval (concat v_21 v_22);
      let (v_24 : expression (bv 16)) <- eval (extract v_4 224 240);
      let (v_25 : expression (bv 16)) <- eval (extract v_6 224 240);
      let v_26 <- eval (concat v_24 v_25);
      let (v_27 : expression (bv 16)) <- eval (extract v_4 240 256);
      let (v_28 : expression (bv 16)) <- eval (extract v_6 240 256);
      let v_29 <- eval (concat v_27 v_28);
      let v_30 <- eval (concat v_26 v_29);
      let v_31 <- eval (concat v_23 v_30);
      let v_32 <- eval (concat v_20 v_31);
      let v_33 <- eval (concat v_17 v_32);
      let v_34 <- eval (concat v_14 v_33);
      let v_35 <- eval (concat v_11 v_34);
      let v_36 <- eval (concat v_8 v_35);
      setRegister (lhs.of_reg ymm_2) v_36;
      pure ()
     action;
    instr_pat $ fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_3 <- getRegister (lhs.of_reg xmm_0);
      let (v_4 : expression (bv 16)) <- eval (extract v_3 64 80);
      let v_5 <- getRegister (lhs.of_reg xmm_1);
      let (v_6 : expression (bv 16)) <- eval (extract v_5 64 80);
      let v_7 <- eval (concat v_4 v_6);
      let (v_8 : expression (bv 16)) <- eval (extract v_3 80 96);
      let (v_9 : expression (bv 16)) <- eval (extract v_5 80 96);
      let v_10 <- eval (concat v_8 v_9);
      let (v_11 : expression (bv 16)) <- eval (extract v_3 96 112);
      let (v_12 : expression (bv 16)) <- eval (extract v_5 96 112);
      let v_13 <- eval (concat v_11 v_12);
      let (v_14 : expression (bv 16)) <- eval (extract v_3 112 128);
      let (v_15 : expression (bv 16)) <- eval (extract v_5 112 128);
      let v_16 <- eval (concat v_14 v_15);
      let v_17 <- eval (concat v_13 v_16);
      let v_18 <- eval (concat v_10 v_17);
      let v_19 <- eval (concat v_7 v_18);
      setRegister (lhs.of_reg xmm_2) v_19;
      pure ()
     action;
    instr_pat $ fun (ymm_0 : reg (bv 256)) (ymm_1 : reg (bv 256)) (ymm_2 : reg (bv 256)) =>
     let action : semantics Unit := do
      let v_3 <- getRegister (lhs.of_reg ymm_0);
      let (v_4 : expression (bv 16)) <- eval (extract v_3 64 80);
      let v_5 <- getRegister (lhs.of_reg ymm_1);
      let (v_6 : expression (bv 16)) <- eval (extract v_5 64 80);
      let v_7 <- eval (concat v_4 v_6);
      let (v_8 : expression (bv 16)) <- eval (extract v_3 80 96);
      let (v_9 : expression (bv 16)) <- eval (extract v_5 80 96);
      let v_10 <- eval (concat v_8 v_9);
      let (v_11 : expression (bv 16)) <- eval (extract v_3 96 112);
      let (v_12 : expression (bv 16)) <- eval (extract v_5 96 112);
      let v_13 <- eval (concat v_11 v_12);
      let (v_14 : expression (bv 16)) <- eval (extract v_3 112 128);
      let (v_15 : expression (bv 16)) <- eval (extract v_5 112 128);
      let v_16 <- eval (concat v_14 v_15);
      let (v_17 : expression (bv 16)) <- eval (extract v_3 192 208);
      let (v_18 : expression (bv 16)) <- eval (extract v_5 192 208);
      let v_19 <- eval (concat v_17 v_18);
      let (v_20 : expression (bv 16)) <- eval (extract v_3 208 224);
      let (v_21 : expression (bv 16)) <- eval (extract v_5 208 224);
      let v_22 <- eval (concat v_20 v_21);
      let (v_23 : expression (bv 16)) <- eval (extract v_3 224 240);
      let (v_24 : expression (bv 16)) <- eval (extract v_5 224 240);
      let v_25 <- eval (concat v_23 v_24);
      let (v_26 : expression (bv 16)) <- eval (extract v_3 240 256);
      let (v_27 : expression (bv 16)) <- eval (extract v_5 240 256);
      let v_28 <- eval (concat v_26 v_27);
      let v_29 <- eval (concat v_25 v_28);
      let v_30 <- eval (concat v_22 v_29);
      let v_31 <- eval (concat v_19 v_30);
      let v_32 <- eval (concat v_16 v_31);
      let v_33 <- eval (concat v_13 v_32);
      let v_34 <- eval (concat v_10 v_33);
      let v_35 <- eval (concat v_7 v_34);
      setRegister (lhs.of_reg ymm_2) v_35;
      pure ()
     action
