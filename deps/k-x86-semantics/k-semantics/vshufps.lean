def vshufps : instruction :=
  definst "vshufps" $ do
    instr_pat $ fun (imm_0 : imm int) (mem_1 : Mem) (xmm_2 : reg (bv 128)) (xmm_3 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_4 <- eval (handleImmediateWithSignExtend imm_0 8 8);
      let v_5 <- eval (isBitSet v_4 0);
      let v_6 <- evaluateAddress mem_1;
      let v_7 <- load v_6 16;
      let (v_8 : expression (bv 32)) <- eval (extract v_7 0 32);
      let (v_9 : expression (bv 32)) <- eval (extract v_7 64 96);
      let (v_10 : expression (bv 32)) <- eval (extract v_7 32 64);
      let (v_11 : expression (bv 32)) <- eval (extract v_7 96 128);
      let v_12 <- eval (isBitSet v_4 2);
      let v_13 <- eval (isBitSet v_4 4);
      let v_14 <- getRegister (lhs.of_reg xmm_2);
      let (v_15 : expression (bv 32)) <- eval (extract v_14 0 32);
      let (v_16 : expression (bv 32)) <- eval (extract v_14 64 96);
      let (v_17 : expression (bv 32)) <- eval (extract v_14 32 64);
      let (v_18 : expression (bv 32)) <- eval (extract v_14 96 128);
      let v_19 <- eval (isBitSet v_4 6);
      let v_20 <- eval (concat (mux (isBitSet v_4 5) (mux v_13 v_15 v_16) (mux v_13 v_17 v_18)) (mux (isBitSet v_4 7) (mux v_19 v_15 v_16) (mux v_19 v_17 v_18)));
      let v_21 <- eval (concat (mux (isBitSet v_4 3) (mux v_12 v_8 v_9) (mux v_12 v_10 v_11)) v_20);
      let v_22 <- eval (concat (mux (isBitSet v_4 1) (mux v_5 v_8 v_9) (mux v_5 v_10 v_11)) v_21);
      setRegister (lhs.of_reg xmm_3) v_22;
      pure ()
     action;
    instr_pat $ fun (imm_0 : imm int) (mem_1 : Mem) (ymm_2 : reg (bv 256)) (ymm_3 : reg (bv 256)) =>
     let action : semantics Unit := do
      let v_4 <- eval (handleImmediateWithSignExtend imm_0 8 8);
      let v_5 <- eval (isBitSet v_4 1);
      let v_6 <- eval (isBitSet v_4 0);
      let v_7 <- evaluateAddress mem_1;
      let v_8 <- load v_7 32;
      let (v_9 : expression (bv 32)) <- eval (extract v_8 0 32);
      let (v_10 : expression (bv 32)) <- eval (extract v_8 64 96);
      let (v_11 : expression (bv 32)) <- eval (extract v_8 32 64);
      let (v_12 : expression (bv 32)) <- eval (extract v_8 96 128);
      let v_13 <- eval (isBitSet v_4 3);
      let v_14 <- eval (isBitSet v_4 2);
      let v_15 <- eval (isBitSet v_4 5);
      let v_16 <- eval (isBitSet v_4 4);
      let v_17 <- getRegister (lhs.of_reg ymm_2);
      let (v_18 : expression (bv 32)) <- eval (extract v_17 0 32);
      let (v_19 : expression (bv 32)) <- eval (extract v_17 64 96);
      let (v_20 : expression (bv 32)) <- eval (extract v_17 32 64);
      let (v_21 : expression (bv 32)) <- eval (extract v_17 96 128);
      let v_22 <- eval (isBitSet v_4 7);
      let v_23 <- eval (isBitSet v_4 6);
      let (v_24 : expression (bv 32)) <- eval (extract v_8 128 160);
      let (v_25 : expression (bv 32)) <- eval (extract v_8 192 224);
      let (v_26 : expression (bv 32)) <- eval (extract v_8 160 192);
      let (v_27 : expression (bv 32)) <- eval (extract v_8 224 256);
      let (v_28 : expression (bv 32)) <- eval (extract v_17 128 160);
      let (v_29 : expression (bv 32)) <- eval (extract v_17 192 224);
      let (v_30 : expression (bv 32)) <- eval (extract v_17 160 192);
      let (v_31 : expression (bv 32)) <- eval (extract v_17 224 256);
      let v_32 <- eval (concat (mux v_15 (mux v_16 v_28 v_29) (mux v_16 v_30 v_31)) (mux v_22 (mux v_23 v_28 v_29) (mux v_23 v_30 v_31)));
      let v_33 <- eval (concat (mux v_13 (mux v_14 v_24 v_25) (mux v_14 v_26 v_27)) v_32);
      let v_34 <- eval (concat (mux v_5 (mux v_6 v_24 v_25) (mux v_6 v_26 v_27)) v_33);
      let v_35 <- eval (concat (mux v_22 (mux v_23 v_18 v_19) (mux v_23 v_20 v_21)) v_34);
      let v_36 <- eval (concat (mux v_15 (mux v_16 v_18 v_19) (mux v_16 v_20 v_21)) v_35);
      let v_37 <- eval (concat (mux v_13 (mux v_14 v_9 v_10) (mux v_14 v_11 v_12)) v_36);
      let v_38 <- eval (concat (mux v_5 (mux v_6 v_9 v_10) (mux v_6 v_11 v_12)) v_37);
      setRegister (lhs.of_reg ymm_3) v_38;
      pure ()
     action;
    instr_pat $ fun (imm_0 : imm int) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) (xmm_3 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_4 <- eval (handleImmediateWithSignExtend imm_0 8 8);
      let v_5 <- eval (isBitSet v_4 0);
      let v_6 <- getRegister (lhs.of_reg xmm_1);
      let (v_7 : expression (bv 32)) <- eval (extract v_6 0 32);
      let (v_8 : expression (bv 32)) <- eval (extract v_6 64 96);
      let (v_9 : expression (bv 32)) <- eval (extract v_6 32 64);
      let (v_10 : expression (bv 32)) <- eval (extract v_6 96 128);
      let v_11 <- eval (isBitSet v_4 2);
      let v_12 <- eval (isBitSet v_4 4);
      let v_13 <- getRegister (lhs.of_reg xmm_2);
      let (v_14 : expression (bv 32)) <- eval (extract v_13 0 32);
      let (v_15 : expression (bv 32)) <- eval (extract v_13 64 96);
      let (v_16 : expression (bv 32)) <- eval (extract v_13 32 64);
      let (v_17 : expression (bv 32)) <- eval (extract v_13 96 128);
      let v_18 <- eval (isBitSet v_4 6);
      let v_19 <- eval (concat (mux (isBitSet v_4 5) (mux v_12 v_14 v_15) (mux v_12 v_16 v_17)) (mux (isBitSet v_4 7) (mux v_18 v_14 v_15) (mux v_18 v_16 v_17)));
      let v_20 <- eval (concat (mux (isBitSet v_4 3) (mux v_11 v_7 v_8) (mux v_11 v_9 v_10)) v_19);
      let v_21 <- eval (concat (mux (isBitSet v_4 1) (mux v_5 v_7 v_8) (mux v_5 v_9 v_10)) v_20);
      setRegister (lhs.of_reg xmm_3) v_21;
      pure ()
     action;
    instr_pat $ fun (imm_0 : imm int) (ymm_1 : reg (bv 256)) (ymm_2 : reg (bv 256)) (ymm_3 : reg (bv 256)) =>
     let action : semantics Unit := do
      let v_4 <- eval (handleImmediateWithSignExtend imm_0 8 8);
      let v_5 <- eval (isBitSet v_4 1);
      let v_6 <- eval (isBitSet v_4 0);
      let v_7 <- getRegister (lhs.of_reg ymm_1);
      let (v_8 : expression (bv 32)) <- eval (extract v_7 0 32);
      let (v_9 : expression (bv 32)) <- eval (extract v_7 64 96);
      let (v_10 : expression (bv 32)) <- eval (extract v_7 32 64);
      let (v_11 : expression (bv 32)) <- eval (extract v_7 96 128);
      let v_12 <- eval (isBitSet v_4 3);
      let v_13 <- eval (isBitSet v_4 2);
      let v_14 <- eval (isBitSet v_4 5);
      let v_15 <- eval (isBitSet v_4 4);
      let v_16 <- getRegister (lhs.of_reg ymm_2);
      let (v_17 : expression (bv 32)) <- eval (extract v_16 0 32);
      let (v_18 : expression (bv 32)) <- eval (extract v_16 64 96);
      let (v_19 : expression (bv 32)) <- eval (extract v_16 32 64);
      let (v_20 : expression (bv 32)) <- eval (extract v_16 96 128);
      let v_21 <- eval (isBitSet v_4 7);
      let v_22 <- eval (isBitSet v_4 6);
      let (v_23 : expression (bv 32)) <- eval (extract v_7 128 160);
      let (v_24 : expression (bv 32)) <- eval (extract v_7 192 224);
      let (v_25 : expression (bv 32)) <- eval (extract v_7 160 192);
      let (v_26 : expression (bv 32)) <- eval (extract v_7 224 256);
      let (v_27 : expression (bv 32)) <- eval (extract v_16 128 160);
      let (v_28 : expression (bv 32)) <- eval (extract v_16 192 224);
      let (v_29 : expression (bv 32)) <- eval (extract v_16 160 192);
      let (v_30 : expression (bv 32)) <- eval (extract v_16 224 256);
      let v_31 <- eval (concat (mux v_14 (mux v_15 v_27 v_28) (mux v_15 v_29 v_30)) (mux v_21 (mux v_22 v_27 v_28) (mux v_22 v_29 v_30)));
      let v_32 <- eval (concat (mux v_12 (mux v_13 v_23 v_24) (mux v_13 v_25 v_26)) v_31);
      let v_33 <- eval (concat (mux v_5 (mux v_6 v_23 v_24) (mux v_6 v_25 v_26)) v_32);
      let v_34 <- eval (concat (mux v_21 (mux v_22 v_17 v_18) (mux v_22 v_19 v_20)) v_33);
      let v_35 <- eval (concat (mux v_14 (mux v_15 v_17 v_18) (mux v_15 v_19 v_20)) v_34);
      let v_36 <- eval (concat (mux v_12 (mux v_13 v_8 v_9) (mux v_13 v_10 v_11)) v_35);
      let v_37 <- eval (concat (mux v_5 (mux v_6 v_8 v_9) (mux v_6 v_10 v_11)) v_36);
      setRegister (lhs.of_reg ymm_3) v_37;
      pure ()
     action
