def vpmaxud : instruction :=
  definst "vpmaxud" $ do
    instr_pat $ fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_3 <- getRegister (lhs.of_reg xmm_1);
      let (v_4 : expression (bv 32)) <- eval (extract v_3 0 32);
      let v_5 <- evaluateAddress mem_0;
      let v_6 <- load v_5 16;
      let (v_7 : expression (bv 32)) <- eval (extract v_6 0 32);
      let (v_8 : expression (bv 32)) <- eval (extract v_3 32 64);
      let (v_9 : expression (bv 32)) <- eval (extract v_6 32 64);
      let (v_10 : expression (bv 32)) <- eval (extract v_3 64 96);
      let (v_11 : expression (bv 32)) <- eval (extract v_6 64 96);
      let (v_12 : expression (bv 32)) <- eval (extract v_3 96 128);
      let (v_13 : expression (bv 32)) <- eval (extract v_6 96 128);
      let v_14 <- eval (concat (mux (ugt v_10 v_11) v_10 v_11) (mux (ugt v_12 v_13) v_12 v_13));
      let v_15 <- eval (concat (mux (ugt v_8 v_9) v_8 v_9) v_14);
      let v_16 <- eval (concat (mux (ugt v_4 v_7) v_4 v_7) v_15);
      setRegister (lhs.of_reg xmm_2) v_16;
      pure ()
     action;
    instr_pat $ fun (mem_0 : Mem) (ymm_1 : reg (bv 256)) (ymm_2 : reg (bv 256)) =>
     let action : semantics Unit := do
      let v_3 <- getRegister (lhs.of_reg ymm_1);
      let (v_4 : expression (bv 32)) <- eval (extract v_3 0 32);
      let v_5 <- evaluateAddress mem_0;
      let v_6 <- load v_5 32;
      let (v_7 : expression (bv 32)) <- eval (extract v_6 0 32);
      let (v_8 : expression (bv 32)) <- eval (extract v_3 32 64);
      let (v_9 : expression (bv 32)) <- eval (extract v_6 32 64);
      let (v_10 : expression (bv 32)) <- eval (extract v_3 64 96);
      let (v_11 : expression (bv 32)) <- eval (extract v_6 64 96);
      let (v_12 : expression (bv 32)) <- eval (extract v_3 96 128);
      let (v_13 : expression (bv 32)) <- eval (extract v_6 96 128);
      let (v_14 : expression (bv 32)) <- eval (extract v_3 128 160);
      let (v_15 : expression (bv 32)) <- eval (extract v_6 128 160);
      let (v_16 : expression (bv 32)) <- eval (extract v_3 160 192);
      let (v_17 : expression (bv 32)) <- eval (extract v_6 160 192);
      let (v_18 : expression (bv 32)) <- eval (extract v_3 192 224);
      let (v_19 : expression (bv 32)) <- eval (extract v_6 192 224);
      let (v_20 : expression (bv 32)) <- eval (extract v_3 224 256);
      let (v_21 : expression (bv 32)) <- eval (extract v_6 224 256);
      let v_22 <- eval (concat (mux (ugt v_18 v_19) v_18 v_19) (mux (ugt v_20 v_21) v_20 v_21));
      let v_23 <- eval (concat (mux (ugt v_16 v_17) v_16 v_17) v_22);
      let v_24 <- eval (concat (mux (ugt v_14 v_15) v_14 v_15) v_23);
      let v_25 <- eval (concat (mux (ugt v_12 v_13) v_12 v_13) v_24);
      let v_26 <- eval (concat (mux (ugt v_10 v_11) v_10 v_11) v_25);
      let v_27 <- eval (concat (mux (ugt v_8 v_9) v_8 v_9) v_26);
      let v_28 <- eval (concat (mux (ugt v_4 v_7) v_4 v_7) v_27);
      setRegister (lhs.of_reg ymm_2) v_28;
      pure ()
     action;
    instr_pat $ fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_3 <- getRegister (lhs.of_reg xmm_1);
      let (v_4 : expression (bv 32)) <- eval (extract v_3 0 32);
      let v_5 <- getRegister (lhs.of_reg xmm_0);
      let (v_6 : expression (bv 32)) <- eval (extract v_5 0 32);
      let (v_7 : expression (bv 32)) <- eval (extract v_3 32 64);
      let (v_8 : expression (bv 32)) <- eval (extract v_5 32 64);
      let (v_9 : expression (bv 32)) <- eval (extract v_3 64 96);
      let (v_10 : expression (bv 32)) <- eval (extract v_5 64 96);
      let (v_11 : expression (bv 32)) <- eval (extract v_3 96 128);
      let (v_12 : expression (bv 32)) <- eval (extract v_5 96 128);
      let v_13 <- eval (concat (mux (ugt v_9 v_10) v_9 v_10) (mux (ugt v_11 v_12) v_11 v_12));
      let v_14 <- eval (concat (mux (ugt v_7 v_8) v_7 v_8) v_13);
      let v_15 <- eval (concat (mux (ugt v_4 v_6) v_4 v_6) v_14);
      setRegister (lhs.of_reg xmm_2) v_15;
      pure ()
     action;
    instr_pat $ fun (ymm_0 : reg (bv 256)) (ymm_1 : reg (bv 256)) (ymm_2 : reg (bv 256)) =>
     let action : semantics Unit := do
      let v_3 <- getRegister (lhs.of_reg ymm_1);
      let (v_4 : expression (bv 32)) <- eval (extract v_3 0 32);
      let v_5 <- getRegister (lhs.of_reg ymm_0);
      let (v_6 : expression (bv 32)) <- eval (extract v_5 0 32);
      let (v_7 : expression (bv 32)) <- eval (extract v_3 32 64);
      let (v_8 : expression (bv 32)) <- eval (extract v_5 32 64);
      let (v_9 : expression (bv 32)) <- eval (extract v_3 64 96);
      let (v_10 : expression (bv 32)) <- eval (extract v_5 64 96);
      let (v_11 : expression (bv 32)) <- eval (extract v_3 96 128);
      let (v_12 : expression (bv 32)) <- eval (extract v_5 96 128);
      let (v_13 : expression (bv 32)) <- eval (extract v_3 128 160);
      let (v_14 : expression (bv 32)) <- eval (extract v_5 128 160);
      let (v_15 : expression (bv 32)) <- eval (extract v_3 160 192);
      let (v_16 : expression (bv 32)) <- eval (extract v_5 160 192);
      let (v_17 : expression (bv 32)) <- eval (extract v_3 192 224);
      let (v_18 : expression (bv 32)) <- eval (extract v_5 192 224);
      let (v_19 : expression (bv 32)) <- eval (extract v_3 224 256);
      let (v_20 : expression (bv 32)) <- eval (extract v_5 224 256);
      let v_21 <- eval (concat (mux (ugt v_17 v_18) v_17 v_18) (mux (ugt v_19 v_20) v_19 v_20));
      let v_22 <- eval (concat (mux (ugt v_15 v_16) v_15 v_16) v_21);
      let v_23 <- eval (concat (mux (ugt v_13 v_14) v_13 v_14) v_22);
      let v_24 <- eval (concat (mux (ugt v_11 v_12) v_11 v_12) v_23);
      let v_25 <- eval (concat (mux (ugt v_9 v_10) v_9 v_10) v_24);
      let v_26 <- eval (concat (mux (ugt v_7 v_8) v_7 v_8) v_25);
      let v_27 <- eval (concat (mux (ugt v_4 v_6) v_4 v_6) v_26);
      setRegister (lhs.of_reg ymm_2) v_27;
      pure ()
     action
