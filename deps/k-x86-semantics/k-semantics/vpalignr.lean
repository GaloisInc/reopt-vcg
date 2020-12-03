def vpalignr : instruction :=
  definst "vpalignr" $ do
    instr_pat $ fun (imm_0 : imm int) (mem_1 : Mem) (xmm_2 : reg (bv 128)) (xmm_3 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_4 <- getRegister (lhs.of_reg xmm_2);
      let v_5 <- evaluateAddress mem_1;
      let v_6 <- load v_5 16;
      let v_7 <- eval (concat v_4 v_6);
      let v_8 <- eval (concat (expression.bv_nat 248 0) (handleImmediateWithSignExtend imm_0 8 8));
      let (v_9 : expression (bv 256)) <- eval (extract (shl v_8 (expression.bv_nat 256 3)) 0 256);
      let (v_10 : expression (bv 128)) <- eval (extract (lshr v_7 v_9) 128 256);
      setRegister (lhs.of_reg xmm_3) v_10;
      pure ()
     action;
    instr_pat $ fun (imm_0 : imm int) (mem_1 : Mem) (ymm_2 : reg (bv 256)) (ymm_3 : reg (bv 256)) =>
     let action : semantics Unit := do
      let v_4 <- getRegister (lhs.of_reg ymm_2);
      let (v_5 : expression (bv 128)) <- eval (extract v_4 0 128);
      let v_6 <- evaluateAddress mem_1;
      let v_7 <- load v_6 32;
      let (v_8 : expression (bv 128)) <- eval (extract v_7 0 128);
      let v_9 <- eval (concat v_5 v_8);
      let v_10 <- eval (concat (expression.bv_nat 248 0) (handleImmediateWithSignExtend imm_0 8 8));
      let (v_11 : expression (bv 256)) <- eval (extract (shl v_10 (expression.bv_nat 256 3)) 0 256);
      let (v_12 : expression (bv 128)) <- eval (extract (lshr v_9 v_11) 128 256);
      let (v_13 : expression (bv 128)) <- eval (extract v_4 128 256);
      let (v_14 : expression (bv 128)) <- eval (extract v_7 128 256);
      let v_15 <- eval (concat v_13 v_14);
      let (v_16 : expression (bv 128)) <- eval (extract (lshr v_15 v_11) 128 256);
      let v_17 <- eval (concat v_12 v_16);
      setRegister (lhs.of_reg ymm_3) v_17;
      pure ()
     action;
    instr_pat $ fun (imm_0 : imm int) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) (xmm_3 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_4 <- getRegister (lhs.of_reg xmm_2);
      let v_5 <- getRegister (lhs.of_reg xmm_1);
      let v_6 <- eval (concat v_4 v_5);
      let v_7 <- eval (concat (expression.bv_nat 248 0) (handleImmediateWithSignExtend imm_0 8 8));
      let (v_8 : expression (bv 256)) <- eval (extract (shl v_7 (expression.bv_nat 256 3)) 0 256);
      let (v_9 : expression (bv 128)) <- eval (extract (lshr v_6 v_8) 128 256);
      setRegister (lhs.of_reg xmm_3) v_9;
      pure ()
     action;
    instr_pat $ fun (imm_0 : imm int) (ymm_1 : reg (bv 256)) (ymm_2 : reg (bv 256)) (ymm_3 : reg (bv 256)) =>
     let action : semantics Unit := do
      let v_4 <- getRegister (lhs.of_reg ymm_2);
      let (v_5 : expression (bv 128)) <- eval (extract v_4 0 128);
      let v_6 <- getRegister (lhs.of_reg ymm_1);
      let (v_7 : expression (bv 128)) <- eval (extract v_6 0 128);
      let v_8 <- eval (concat v_5 v_7);
      let v_9 <- eval (concat (expression.bv_nat 248 0) (handleImmediateWithSignExtend imm_0 8 8));
      let (v_10 : expression (bv 256)) <- eval (extract (shl v_9 (expression.bv_nat 256 3)) 0 256);
      let (v_11 : expression (bv 128)) <- eval (extract (lshr v_8 v_10) 128 256);
      let (v_12 : expression (bv 128)) <- eval (extract v_4 128 256);
      let (v_13 : expression (bv 128)) <- eval (extract v_6 128 256);
      let v_14 <- eval (concat v_12 v_13);
      let (v_15 : expression (bv 128)) <- eval (extract (lshr v_14 v_10) 128 256);
      let v_16 <- eval (concat v_11 v_15);
      setRegister (lhs.of_reg ymm_3) v_16;
      pure ()
     action
