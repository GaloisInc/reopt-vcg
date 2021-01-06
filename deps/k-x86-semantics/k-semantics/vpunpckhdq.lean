def vpunpckhdq : instruction :=
  definst "vpunpckhdq" $ do
    instr_pat $ fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_3 <- evaluateAddress mem_0;
      let v_4 <- load v_3 16;
      let (v_5 : expression (bv 32)) <- eval (extract v_4 0 32);
      let v_6 <- getRegister (lhs.of_reg xmm_1);
      let (v_7 : expression (bv 32)) <- eval (extract v_6 0 32);
      let v_8 <- eval (concat v_5 v_7);
      let (v_9 : expression (bv 32)) <- eval (extract v_4 32 64);
      let (v_10 : expression (bv 32)) <- eval (extract v_6 32 64);
      let v_11 <- eval (concat v_9 v_10);
      let v_12 <- eval (concat v_8 v_11);
      setRegister (lhs.of_reg xmm_2) v_12;
      pure ()
     action;
    instr_pat $ fun (mem_0 : Mem) (ymm_1 : reg (bv 256)) (ymm_2 : reg (bv 256)) =>
     let action : semantics Unit := do
      let v_3 <- evaluateAddress mem_0;
      let v_4 <- load v_3 32;
      let (v_5 : expression (bv 32)) <- eval (extract v_4 0 32);
      let v_6 <- getRegister (lhs.of_reg ymm_1);
      let (v_7 : expression (bv 32)) <- eval (extract v_6 0 32);
      let v_8 <- eval (concat v_5 v_7);
      let (v_9 : expression (bv 32)) <- eval (extract v_4 32 64);
      let (v_10 : expression (bv 32)) <- eval (extract v_6 32 64);
      let v_11 <- eval (concat v_9 v_10);
      let (v_12 : expression (bv 32)) <- eval (extract v_4 128 160);
      let (v_13 : expression (bv 32)) <- eval (extract v_6 128 160);
      let v_14 <- eval (concat v_12 v_13);
      let (v_15 : expression (bv 32)) <- eval (extract v_4 160 192);
      let (v_16 : expression (bv 32)) <- eval (extract v_6 160 192);
      let v_17 <- eval (concat v_15 v_16);
      let v_18 <- eval (concat v_14 v_17);
      let v_19 <- eval (concat v_11 v_18);
      let v_20 <- eval (concat v_8 v_19);
      setRegister (lhs.of_reg ymm_2) v_20;
      pure ()
     action;
    instr_pat $ fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_3 <- getRegister (lhs.of_reg xmm_0);
      let (v_4 : expression (bv 32)) <- eval (extract v_3 0 32);
      let v_5 <- getRegister (lhs.of_reg xmm_1);
      let (v_6 : expression (bv 32)) <- eval (extract v_5 0 32);
      let v_7 <- eval (concat v_4 v_6);
      let (v_8 : expression (bv 32)) <- eval (extract v_3 32 64);
      let (v_9 : expression (bv 32)) <- eval (extract v_5 32 64);
      let v_10 <- eval (concat v_8 v_9);
      let v_11 <- eval (concat v_7 v_10);
      setRegister (lhs.of_reg xmm_2) v_11;
      pure ()
     action;
    instr_pat $ fun (ymm_0 : reg (bv 256)) (ymm_1 : reg (bv 256)) (ymm_2 : reg (bv 256)) =>
     let action : semantics Unit := do
      let v_3 <- getRegister (lhs.of_reg ymm_0);
      let (v_4 : expression (bv 32)) <- eval (extract v_3 0 32);
      let v_5 <- getRegister (lhs.of_reg ymm_1);
      let (v_6 : expression (bv 32)) <- eval (extract v_5 0 32);
      let v_7 <- eval (concat v_4 v_6);
      let (v_8 : expression (bv 32)) <- eval (extract v_3 32 64);
      let (v_9 : expression (bv 32)) <- eval (extract v_5 32 64);
      let v_10 <- eval (concat v_8 v_9);
      let (v_11 : expression (bv 32)) <- eval (extract v_3 128 160);
      let (v_12 : expression (bv 32)) <- eval (extract v_5 128 160);
      let v_13 <- eval (concat v_11 v_12);
      let (v_14 : expression (bv 32)) <- eval (extract v_3 160 192);
      let (v_15 : expression (bv 32)) <- eval (extract v_5 160 192);
      let v_16 <- eval (concat v_14 v_15);
      let v_17 <- eval (concat v_13 v_16);
      let v_18 <- eval (concat v_10 v_17);
      let v_19 <- eval (concat v_7 v_18);
      setRegister (lhs.of_reg ymm_2) v_19;
      pure ()
     action
