def psrad : instruction :=
  definst "psrad" $ do
    instr_pat $ fun (imm_0 : imm int) (xmm_1 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_2 <- getRegister (lhs.of_reg xmm_1);
      let (v_3 : expression (bv 32)) <- eval (extract v_2 0 32);
      let v_4 <- eval (handleImmediateWithSignExtend imm_0 8 8);
      let v_5 <- eval (concat (expression.bv_nat 56 0) v_4);
      let v_6 <- eval (concat (expression.bv_nat 24 0) v_4);
      let v_7 <- eval (mux (ugt v_5 (expression.bv_nat 64 31)) (expression.bv_nat 32 32) v_6);
      let (v_8 : expression (bv 32)) <- eval (extract v_2 32 64);
      let (v_9 : expression (bv 32)) <- eval (extract v_2 64 96);
      let (v_10 : expression (bv 32)) <- eval (extract v_2 96 128);
      let v_11 <- eval (concat (ashr v_9 v_7) (ashr v_10 v_7));
      let v_12 <- eval (concat (ashr v_8 v_7) v_11);
      let v_13 <- eval (concat (ashr v_3 v_7) v_12);
      setRegister (lhs.of_reg xmm_1) v_13;
      pure ()
     action;
    instr_pat $ fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_2 <- getRegister (lhs.of_reg xmm_1);
      let (v_3 : expression (bv 32)) <- eval (extract v_2 0 32);
      let v_4 <- evaluateAddress mem_0;
      let v_5 <- load v_4 16;
      let (v_6 : expression (bv 64)) <- eval (extract v_5 64 128);
      let (v_7 : expression (bv 32)) <- eval (extract v_5 96 128);
      let v_8 <- eval (mux (ugt v_6 (expression.bv_nat 64 31)) (expression.bv_nat 32 32) v_7);
      let (v_9 : expression (bv 32)) <- eval (extract v_2 32 64);
      let (v_10 : expression (bv 32)) <- eval (extract v_2 64 96);
      let (v_11 : expression (bv 32)) <- eval (extract v_2 96 128);
      let v_12 <- eval (concat (ashr v_10 v_8) (ashr v_11 v_8));
      let v_13 <- eval (concat (ashr v_9 v_8) v_12);
      let v_14 <- eval (concat (ashr v_3 v_8) v_13);
      setRegister (lhs.of_reg xmm_1) v_14;
      pure ()
     action;
    instr_pat $ fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_2 <- getRegister (lhs.of_reg xmm_1);
      let (v_3 : expression (bv 32)) <- eval (extract v_2 0 32);
      let v_4 <- getRegister (lhs.of_reg xmm_0);
      let (v_5 : expression (bv 64)) <- eval (extract v_4 64 128);
      let (v_6 : expression (bv 32)) <- eval (extract v_4 96 128);
      let v_7 <- eval (mux (ugt v_5 (expression.bv_nat 64 31)) (expression.bv_nat 32 32) v_6);
      let (v_8 : expression (bv 32)) <- eval (extract v_2 32 64);
      let (v_9 : expression (bv 32)) <- eval (extract v_2 64 96);
      let (v_10 : expression (bv 32)) <- eval (extract v_2 96 128);
      let v_11 <- eval (concat (ashr v_9 v_7) (ashr v_10 v_7));
      let v_12 <- eval (concat (ashr v_8 v_7) v_11);
      let v_13 <- eval (concat (ashr v_3 v_7) v_12);
      setRegister (lhs.of_reg xmm_1) v_13;
      pure ()
     action
