def vunpcklps : instruction :=
  definst "vunpcklps" $ do
    instr_pat $ fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_3 <- evaluateAddress mem_0;
      let v_4 <- load v_3 16;
      let (v_5 : expression (bv 32)) <- eval (extract v_4 64 96);
      let v_6 <- getRegister (lhs.of_reg xmm_1);
      let (v_7 : expression (bv 32)) <- eval (extract v_6 64 96);
      let v_8 <- eval (concat v_5 v_7);
      let (v_9 : expression (bv 32)) <- eval (extract v_4 96 128);
      let v_10 <- eval (concat v_8 v_9);
      let (v_11 : expression (bv 32)) <- eval (extract v_6 96 128);
      let v_12 <- eval (concat v_10 v_11);
      setRegister (lhs.of_reg xmm_2) v_12;
      pure ()
     action;
    instr_pat $ fun (mem_0 : Mem) (ymm_1 : reg (bv 256)) (ymm_2 : reg (bv 256)) =>
     let action : semantics Unit := do
      let v_3 <- evaluateAddress mem_0;
      let v_4 <- load v_3 32;
      let (v_5 : expression (bv 32)) <- eval (extract v_4 64 96);
      let v_6 <- getRegister (lhs.of_reg ymm_1);
      let (v_7 : expression (bv 32)) <- eval (extract v_6 64 96);
      let v_8 <- eval (concat v_5 v_7);
      let (v_9 : expression (bv 32)) <- eval (extract v_4 96 128);
      let v_10 <- eval (concat v_8 v_9);
      let (v_11 : expression (bv 32)) <- eval (extract v_6 96 128);
      let v_12 <- eval (concat v_10 v_11);
      let (v_13 : expression (bv 32)) <- eval (extract v_4 192 224);
      let (v_14 : expression (bv 32)) <- eval (extract v_6 192 224);
      let v_15 <- eval (concat v_13 v_14);
      let (v_16 : expression (bv 32)) <- eval (extract v_4 224 256);
      let v_17 <- eval (concat v_15 v_16);
      let (v_18 : expression (bv 32)) <- eval (extract v_6 224 256);
      let v_19 <- eval (concat v_17 v_18);
      let v_20 <- eval (concat v_12 v_19);
      setRegister (lhs.of_reg ymm_2) v_20;
      pure ()
     action;
    instr_pat $ fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_3 <- getRegister (lhs.of_reg xmm_0);
      let (v_4 : expression (bv 32)) <- eval (extract v_3 64 96);
      let v_5 <- getRegister (lhs.of_reg xmm_1);
      let (v_6 : expression (bv 32)) <- eval (extract v_5 64 96);
      let v_7 <- eval (concat v_4 v_6);
      let (v_8 : expression (bv 32)) <- eval (extract v_3 96 128);
      let v_9 <- eval (concat v_7 v_8);
      let (v_10 : expression (bv 32)) <- eval (extract v_5 96 128);
      let v_11 <- eval (concat v_9 v_10);
      setRegister (lhs.of_reg xmm_2) v_11;
      pure ()
     action;
    instr_pat $ fun (ymm_0 : reg (bv 256)) (ymm_1 : reg (bv 256)) (ymm_2 : reg (bv 256)) =>
     let action : semantics Unit := do
      let v_3 <- getRegister (lhs.of_reg ymm_0);
      let (v_4 : expression (bv 32)) <- eval (extract v_3 64 96);
      let v_5 <- getRegister (lhs.of_reg ymm_1);
      let (v_6 : expression (bv 32)) <- eval (extract v_5 64 96);
      let v_7 <- eval (concat v_4 v_6);
      let (v_8 : expression (bv 32)) <- eval (extract v_3 96 128);
      let v_9 <- eval (concat v_7 v_8);
      let (v_10 : expression (bv 32)) <- eval (extract v_5 96 128);
      let v_11 <- eval (concat v_9 v_10);
      let (v_12 : expression (bv 32)) <- eval (extract v_3 192 224);
      let (v_13 : expression (bv 32)) <- eval (extract v_5 192 224);
      let v_14 <- eval (concat v_12 v_13);
      let (v_15 : expression (bv 32)) <- eval (extract v_3 224 256);
      let v_16 <- eval (concat v_14 v_15);
      let (v_17 : expression (bv 32)) <- eval (extract v_5 224 256);
      let v_18 <- eval (concat v_16 v_17);
      let v_19 <- eval (concat v_11 v_18);
      setRegister (lhs.of_reg ymm_2) v_19;
      pure ()
     action
