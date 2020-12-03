def vpsrlq : instruction :=
  definst "vpsrlq" $ do
    instr_pat $ fun (imm_0 : imm int) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_3 <- eval (concat (expression.bv_nat 56 0) (handleImmediateWithSignExtend imm_0 8 8));
      let v_4 <- getRegister (lhs.of_reg xmm_1);
      let (v_5 : expression (bv 64)) <- eval (extract v_4 0 64);
      let (v_6 : expression (bv 64)) <- eval (extract v_4 64 128);
      let v_7 <- eval (concat (lshr v_5 v_3) (lshr v_6 v_3));
      setRegister (lhs.of_reg xmm_2) (mux (ugt v_3 (expression.bv_nat 64 63)) (expression.bv_nat 128 0) v_7);
      pure ()
     action;
    instr_pat $ fun (imm_0 : imm int) (ymm_1 : reg (bv 256)) (ymm_2 : reg (bv 256)) =>
     let action : semantics Unit := do
      let v_3 <- eval (concat (expression.bv_nat 56 0) (handleImmediateWithSignExtend imm_0 8 8));
      let v_4 <- getRegister (lhs.of_reg ymm_1);
      let (v_5 : expression (bv 64)) <- eval (extract v_4 0 64);
      let (v_6 : expression (bv 64)) <- eval (extract v_4 64 128);
      let (v_7 : expression (bv 64)) <- eval (extract v_4 128 192);
      let (v_8 : expression (bv 64)) <- eval (extract v_4 192 256);
      let v_9 <- eval (concat (lshr v_7 v_3) (lshr v_8 v_3));
      let v_10 <- eval (concat (lshr v_6 v_3) v_9);
      let v_11 <- eval (concat (lshr v_5 v_3) v_10);
      setRegister (lhs.of_reg ymm_2) (mux (ugt v_3 (expression.bv_nat 64 63)) (expression.bv_nat 256 0) v_11);
      pure ()
     action;
    instr_pat $ fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_3 <- evaluateAddress mem_0;
      let v_4 <- load v_3 16;
      let (v_5 : expression (bv 64)) <- eval (extract v_4 64 128);
      let v_6 <- getRegister (lhs.of_reg xmm_1);
      let (v_7 : expression (bv 64)) <- eval (extract v_6 0 64);
      let (v_8 : expression (bv 64)) <- eval (extract v_6 64 128);
      let v_9 <- eval (concat (lshr v_7 v_5) (lshr v_8 v_5));
      setRegister (lhs.of_reg xmm_2) (mux (ugt v_5 (expression.bv_nat 64 63)) (expression.bv_nat 128 0) v_9);
      pure ()
     action;
    instr_pat $ fun (mem_0 : Mem) (ymm_1 : reg (bv 256)) (ymm_2 : reg (bv 256)) =>
     let action : semantics Unit := do
      let v_3 <- evaluateAddress mem_0;
      let v_4 <- load v_3 16;
      let (v_5 : expression (bv 64)) <- eval (extract v_4 64 128);
      let v_6 <- getRegister (lhs.of_reg ymm_1);
      let (v_7 : expression (bv 64)) <- eval (extract v_6 0 64);
      let (v_8 : expression (bv 64)) <- eval (extract v_6 64 128);
      let (v_9 : expression (bv 64)) <- eval (extract v_6 128 192);
      let (v_10 : expression (bv 64)) <- eval (extract v_6 192 256);
      let v_11 <- eval (concat (lshr v_9 v_5) (lshr v_10 v_5));
      let v_12 <- eval (concat (lshr v_8 v_5) v_11);
      let v_13 <- eval (concat (lshr v_7 v_5) v_12);
      setRegister (lhs.of_reg ymm_2) (mux (ugt v_5 (expression.bv_nat 64 63)) (expression.bv_nat 256 0) v_13);
      pure ()
     action;
    instr_pat $ fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_3 <- getRegister (lhs.of_reg xmm_0);
      let (v_4 : expression (bv 64)) <- eval (extract v_3 64 128);
      let v_5 <- getRegister (lhs.of_reg xmm_1);
      let (v_6 : expression (bv 64)) <- eval (extract v_5 0 64);
      let (v_7 : expression (bv 64)) <- eval (extract v_5 64 128);
      let v_8 <- eval (concat (lshr v_6 v_4) (lshr v_7 v_4));
      setRegister (lhs.of_reg xmm_2) (mux (ugt v_4 (expression.bv_nat 64 63)) (expression.bv_nat 128 0) v_8);
      pure ()
     action;
    instr_pat $ fun (xmm_0 : reg (bv 128)) (ymm_1 : reg (bv 256)) (ymm_2 : reg (bv 256)) =>
     let action : semantics Unit := do
      let v_3 <- getRegister (lhs.of_reg xmm_0);
      let (v_4 : expression (bv 64)) <- eval (extract v_3 64 128);
      let v_5 <- getRegister (lhs.of_reg ymm_1);
      let (v_6 : expression (bv 64)) <- eval (extract v_5 0 64);
      let (v_7 : expression (bv 64)) <- eval (extract v_5 64 128);
      let (v_8 : expression (bv 64)) <- eval (extract v_5 128 192);
      let (v_9 : expression (bv 64)) <- eval (extract v_5 192 256);
      let v_10 <- eval (concat (lshr v_8 v_4) (lshr v_9 v_4));
      let v_11 <- eval (concat (lshr v_7 v_4) v_10);
      let v_12 <- eval (concat (lshr v_6 v_4) v_11);
      setRegister (lhs.of_reg ymm_2) (mux (ugt v_4 (expression.bv_nat 64 63)) (expression.bv_nat 256 0) v_12);
      pure ()
     action
