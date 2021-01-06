def psraw : instruction :=
  definst "psraw" $ do
    instr_pat $ fun (imm_0 : imm int) (xmm_1 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_2 <- getRegister (lhs.of_reg xmm_1);
      let (v_3 : expression (bv 16)) <- eval (extract v_2 0 16);
      let v_4 <- eval (handleImmediateWithSignExtend imm_0 8 8);
      let v_5 <- eval (concat (expression.bv_nat 56 0) v_4);
      let v_6 <- eval (concat (expression.bv_nat 8 0) v_4);
      let v_7 <- eval (mux (ugt v_5 (expression.bv_nat 64 15)) (expression.bv_nat 16 16) v_6);
      let (v_8 : expression (bv 16)) <- eval (extract v_2 16 32);
      let (v_9 : expression (bv 16)) <- eval (extract v_2 32 48);
      let (v_10 : expression (bv 16)) <- eval (extract v_2 48 64);
      let (v_11 : expression (bv 16)) <- eval (extract v_2 64 80);
      let (v_12 : expression (bv 16)) <- eval (extract v_2 80 96);
      let (v_13 : expression (bv 16)) <- eval (extract v_2 96 112);
      let (v_14 : expression (bv 16)) <- eval (extract v_2 112 128);
      let v_15 <- eval (concat (ashr v_13 v_7) (ashr v_14 v_7));
      let v_16 <- eval (concat (ashr v_12 v_7) v_15);
      let v_17 <- eval (concat (ashr v_11 v_7) v_16);
      let v_18 <- eval (concat (ashr v_10 v_7) v_17);
      let v_19 <- eval (concat (ashr v_9 v_7) v_18);
      let v_20 <- eval (concat (ashr v_8 v_7) v_19);
      let v_21 <- eval (concat (ashr v_3 v_7) v_20);
      setRegister (lhs.of_reg xmm_1) v_21;
      pure ()
     action;
    instr_pat $ fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_2 <- getRegister (lhs.of_reg xmm_1);
      let (v_3 : expression (bv 16)) <- eval (extract v_2 0 16);
      let v_4 <- evaluateAddress mem_0;
      let v_5 <- load v_4 16;
      let (v_6 : expression (bv 64)) <- eval (extract v_5 64 128);
      let (v_7 : expression (bv 16)) <- eval (extract v_5 112 128);
      let v_8 <- eval (mux (ugt v_6 (expression.bv_nat 64 15)) (expression.bv_nat 16 16) v_7);
      let (v_9 : expression (bv 16)) <- eval (extract v_2 16 32);
      let (v_10 : expression (bv 16)) <- eval (extract v_2 32 48);
      let (v_11 : expression (bv 16)) <- eval (extract v_2 48 64);
      let (v_12 : expression (bv 16)) <- eval (extract v_2 64 80);
      let (v_13 : expression (bv 16)) <- eval (extract v_2 80 96);
      let (v_14 : expression (bv 16)) <- eval (extract v_2 96 112);
      let (v_15 : expression (bv 16)) <- eval (extract v_2 112 128);
      let v_16 <- eval (concat (ashr v_14 v_8) (ashr v_15 v_8));
      let v_17 <- eval (concat (ashr v_13 v_8) v_16);
      let v_18 <- eval (concat (ashr v_12 v_8) v_17);
      let v_19 <- eval (concat (ashr v_11 v_8) v_18);
      let v_20 <- eval (concat (ashr v_10 v_8) v_19);
      let v_21 <- eval (concat (ashr v_9 v_8) v_20);
      let v_22 <- eval (concat (ashr v_3 v_8) v_21);
      setRegister (lhs.of_reg xmm_1) v_22;
      pure ()
     action;
    instr_pat $ fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_2 <- getRegister (lhs.of_reg xmm_1);
      let (v_3 : expression (bv 16)) <- eval (extract v_2 0 16);
      let v_4 <- getRegister (lhs.of_reg xmm_0);
      let (v_5 : expression (bv 64)) <- eval (extract v_4 64 128);
      let (v_6 : expression (bv 16)) <- eval (extract v_4 112 128);
      let v_7 <- eval (mux (ugt v_5 (expression.bv_nat 64 15)) (expression.bv_nat 16 16) v_6);
      let (v_8 : expression (bv 16)) <- eval (extract v_2 16 32);
      let (v_9 : expression (bv 16)) <- eval (extract v_2 32 48);
      let (v_10 : expression (bv 16)) <- eval (extract v_2 48 64);
      let (v_11 : expression (bv 16)) <- eval (extract v_2 64 80);
      let (v_12 : expression (bv 16)) <- eval (extract v_2 80 96);
      let (v_13 : expression (bv 16)) <- eval (extract v_2 96 112);
      let (v_14 : expression (bv 16)) <- eval (extract v_2 112 128);
      let v_15 <- eval (concat (ashr v_13 v_7) (ashr v_14 v_7));
      let v_16 <- eval (concat (ashr v_12 v_7) v_15);
      let v_17 <- eval (concat (ashr v_11 v_7) v_16);
      let v_18 <- eval (concat (ashr v_10 v_7) v_17);
      let v_19 <- eval (concat (ashr v_9 v_7) v_18);
      let v_20 <- eval (concat (ashr v_8 v_7) v_19);
      let v_21 <- eval (concat (ashr v_3 v_7) v_20);
      setRegister (lhs.of_reg xmm_1) v_21;
      pure ()
     action
