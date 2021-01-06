def psrlw : instruction :=
  definst "psrlw" $ do
    instr_pat $ fun (imm_0 : imm int) (xmm_1 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_2 <- eval (handleImmediateWithSignExtend imm_0 8 8);
      let v_3 <- eval (concat (expression.bv_nat 56 0) v_2);
      let v_4 <- getRegister (lhs.of_reg xmm_1);
      let (v_5 : expression (bv 16)) <- eval (extract v_4 0 16);
      let v_6 <- eval (concat (expression.bv_nat 8 0) v_2);
      let (v_7 : expression (bv 16)) <- eval (extract v_4 16 32);
      let (v_8 : expression (bv 16)) <- eval (extract v_4 32 48);
      let (v_9 : expression (bv 16)) <- eval (extract v_4 48 64);
      let (v_10 : expression (bv 16)) <- eval (extract v_4 64 80);
      let (v_11 : expression (bv 16)) <- eval (extract v_4 80 96);
      let (v_12 : expression (bv 16)) <- eval (extract v_4 96 112);
      let (v_13 : expression (bv 16)) <- eval (extract v_4 112 128);
      let v_14 <- eval (concat (lshr v_12 v_6) (lshr v_13 v_6));
      let v_15 <- eval (concat (lshr v_11 v_6) v_14);
      let v_16 <- eval (concat (lshr v_10 v_6) v_15);
      let v_17 <- eval (concat (lshr v_9 v_6) v_16);
      let v_18 <- eval (concat (lshr v_8 v_6) v_17);
      let v_19 <- eval (concat (lshr v_7 v_6) v_18);
      let v_20 <- eval (concat (lshr v_5 v_6) v_19);
      setRegister (lhs.of_reg xmm_1) (mux (ugt v_3 (expression.bv_nat 64 15)) (expression.bv_nat 128 0) v_20);
      pure ()
     action;
    instr_pat $ fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_2 <- evaluateAddress mem_0;
      let v_3 <- load v_2 16;
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
      setRegister (lhs.of_reg xmm_1) (mux (ugt v_4 (expression.bv_nat 64 15)) (expression.bv_nat 128 0) v_21);
      pure ()
     action;
    instr_pat $ fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_2 <- getRegister (lhs.of_reg xmm_0);
      let (v_3 : expression (bv 64)) <- eval (extract v_2 64 128);
      let v_4 <- getRegister (lhs.of_reg xmm_1);
      let (v_5 : expression (bv 16)) <- eval (extract v_4 0 16);
      let (v_6 : expression (bv 16)) <- eval (extract v_2 112 128);
      let (v_7 : expression (bv 16)) <- eval (extract v_4 16 32);
      let (v_8 : expression (bv 16)) <- eval (extract v_4 32 48);
      let (v_9 : expression (bv 16)) <- eval (extract v_4 48 64);
      let (v_10 : expression (bv 16)) <- eval (extract v_4 64 80);
      let (v_11 : expression (bv 16)) <- eval (extract v_4 80 96);
      let (v_12 : expression (bv 16)) <- eval (extract v_4 96 112);
      let (v_13 : expression (bv 16)) <- eval (extract v_4 112 128);
      let v_14 <- eval (concat (lshr v_12 v_6) (lshr v_13 v_6));
      let v_15 <- eval (concat (lshr v_11 v_6) v_14);
      let v_16 <- eval (concat (lshr v_10 v_6) v_15);
      let v_17 <- eval (concat (lshr v_9 v_6) v_16);
      let v_18 <- eval (concat (lshr v_8 v_6) v_17);
      let v_19 <- eval (concat (lshr v_7 v_6) v_18);
      let v_20 <- eval (concat (lshr v_5 v_6) v_19);
      setRegister (lhs.of_reg xmm_1) (mux (ugt v_3 (expression.bv_nat 64 15)) (expression.bv_nat 128 0) v_20);
      pure ()
     action
