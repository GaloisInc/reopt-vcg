def vpbroadcastw : instruction :=
  definst "vpbroadcastw" $ do
    instr_pat $ fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_2 <- evaluateAddress mem_0;
      let v_3 <- load v_2 2;
      let v_4 <- eval (concat v_3 v_3);
      let v_5 <- eval (concat v_3 v_4);
      let v_6 <- eval (concat v_3 v_5);
      let v_7 <- eval (concat v_3 v_6);
      let v_8 <- eval (concat v_3 v_7);
      let v_9 <- eval (concat v_3 v_8);
      let v_10 <- eval (concat v_3 v_9);
      setRegister (lhs.of_reg xmm_1) v_10;
      pure ()
     action;
    instr_pat $ fun (mem_0 : Mem) (ymm_1 : reg (bv 256)) =>
     let action : semantics Unit := do
      let v_2 <- evaluateAddress mem_0;
      let v_3 <- load v_2 2;
      let v_4 <- eval (concat v_3 v_3);
      let v_5 <- eval (concat v_3 v_4);
      let v_6 <- eval (concat v_3 v_5);
      let v_7 <- eval (concat v_3 v_6);
      let v_8 <- eval (concat v_3 v_7);
      let v_9 <- eval (concat v_3 v_8);
      let v_10 <- eval (concat v_3 v_9);
      let v_11 <- eval (concat v_3 v_10);
      let v_12 <- eval (concat v_3 v_11);
      let v_13 <- eval (concat v_3 v_12);
      let v_14 <- eval (concat v_3 v_13);
      let v_15 <- eval (concat v_3 v_14);
      let v_16 <- eval (concat v_3 v_15);
      let v_17 <- eval (concat v_3 v_16);
      let v_18 <- eval (concat v_3 v_17);
      setRegister (lhs.of_reg ymm_1) v_18;
      pure ()
     action;
    instr_pat $ fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_2 <- getRegister (lhs.of_reg xmm_0);
      let (v_3 : expression (bv 16)) <- eval (extract v_2 112 128);
      let v_4 <- eval (concat v_3 v_3);
      let v_5 <- eval (concat v_3 v_4);
      let v_6 <- eval (concat v_3 v_5);
      let v_7 <- eval (concat v_3 v_6);
      let v_8 <- eval (concat v_3 v_7);
      let v_9 <- eval (concat v_3 v_8);
      let v_10 <- eval (concat v_3 v_9);
      setRegister (lhs.of_reg xmm_1) v_10;
      pure ()
     action;
    instr_pat $ fun (xmm_0 : reg (bv 128)) (ymm_1 : reg (bv 256)) =>
     let action : semantics Unit := do
      let v_2 <- getRegister (lhs.of_reg xmm_0);
      let (v_3 : expression (bv 16)) <- eval (extract v_2 112 128);
      let v_4 <- eval (concat v_3 v_3);
      let v_5 <- eval (concat v_3 v_4);
      let v_6 <- eval (concat v_3 v_5);
      let v_7 <- eval (concat v_3 v_6);
      let v_8 <- eval (concat v_3 v_7);
      let v_9 <- eval (concat v_3 v_8);
      let v_10 <- eval (concat v_3 v_9);
      let v_11 <- eval (concat v_3 v_10);
      let v_12 <- eval (concat v_3 v_11);
      let v_13 <- eval (concat v_3 v_12);
      let v_14 <- eval (concat v_3 v_13);
      let v_15 <- eval (concat v_3 v_14);
      let v_16 <- eval (concat v_3 v_15);
      let v_17 <- eval (concat v_3 v_16);
      let v_18 <- eval (concat v_3 v_17);
      setRegister (lhs.of_reg ymm_1) v_18;
      pure ()
     action
