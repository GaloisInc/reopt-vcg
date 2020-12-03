def pslld : instruction :=
  definst "pslld" $ do
    instr_pat $ fun (imm_0 : imm int) (xmm_1 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_2 <- eval (handleImmediateWithSignExtend imm_0 8 8);
      let v_3 <- eval (concat (expression.bv_nat 56 0) v_2);
      let v_4 <- getRegister (lhs.of_reg xmm_1);
      let (v_5 : expression (bv 32)) <- eval (extract v_4 0 32);
      let v_6 <- eval (concat (expression.bv_nat 24 0) v_2);
      let (v_7 : expression (bv 32)) <- eval (extract (shl v_5 v_6) 0 32);
      let (v_8 : expression (bv 32)) <- eval (extract v_4 32 64);
      let (v_9 : expression (bv 32)) <- eval (extract (shl v_8 v_6) 0 32);
      let (v_10 : expression (bv 32)) <- eval (extract v_4 64 96);
      let (v_11 : expression (bv 32)) <- eval (extract (shl v_10 v_6) 0 32);
      let (v_12 : expression (bv 32)) <- eval (extract v_4 96 128);
      let (v_13 : expression (bv 32)) <- eval (extract (shl v_12 v_6) 0 32);
      let v_14 <- eval (concat v_11 v_13);
      let v_15 <- eval (concat v_9 v_14);
      let v_16 <- eval (concat v_7 v_15);
      setRegister (lhs.of_reg xmm_1) (mux (ugt v_3 (expression.bv_nat 64 31)) (expression.bv_nat 128 0) v_16);
      pure ()
     action;
    instr_pat $ fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_2 <- evaluateAddress mem_0;
      let v_3 <- load v_2 16;
      let (v_4 : expression (bv 64)) <- eval (extract v_3 64 128);
      let v_5 <- getRegister (lhs.of_reg xmm_1);
      let (v_6 : expression (bv 32)) <- eval (extract v_5 0 32);
      let (v_7 : expression (bv 32)) <- eval (extract v_3 96 128);
      let (v_8 : expression (bv 32)) <- eval (extract (shl v_6 v_7) 0 32);
      let (v_9 : expression (bv 32)) <- eval (extract v_5 32 64);
      let (v_10 : expression (bv 32)) <- eval (extract (shl v_9 v_7) 0 32);
      let (v_11 : expression (bv 32)) <- eval (extract v_5 64 96);
      let (v_12 : expression (bv 32)) <- eval (extract (shl v_11 v_7) 0 32);
      let (v_13 : expression (bv 32)) <- eval (extract v_5 96 128);
      let (v_14 : expression (bv 32)) <- eval (extract (shl v_13 v_7) 0 32);
      let v_15 <- eval (concat v_12 v_14);
      let v_16 <- eval (concat v_10 v_15);
      let v_17 <- eval (concat v_8 v_16);
      setRegister (lhs.of_reg xmm_1) (mux (ugt v_4 (expression.bv_nat 64 31)) (expression.bv_nat 128 0) v_17);
      pure ()
     action;
    instr_pat $ fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_2 <- getRegister (lhs.of_reg xmm_0);
      let (v_3 : expression (bv 64)) <- eval (extract v_2 64 128);
      let v_4 <- getRegister (lhs.of_reg xmm_1);
      let (v_5 : expression (bv 32)) <- eval (extract v_4 0 32);
      let (v_6 : expression (bv 32)) <- eval (extract v_2 96 128);
      let (v_7 : expression (bv 32)) <- eval (extract (shl v_5 v_6) 0 32);
      let (v_8 : expression (bv 32)) <- eval (extract v_4 32 64);
      let (v_9 : expression (bv 32)) <- eval (extract (shl v_8 v_6) 0 32);
      let (v_10 : expression (bv 32)) <- eval (extract v_4 64 96);
      let (v_11 : expression (bv 32)) <- eval (extract (shl v_10 v_6) 0 32);
      let (v_12 : expression (bv 32)) <- eval (extract v_4 96 128);
      let (v_13 : expression (bv 32)) <- eval (extract (shl v_12 v_6) 0 32);
      let v_14 <- eval (concat v_11 v_13);
      let v_15 <- eval (concat v_9 v_14);
      let v_16 <- eval (concat v_7 v_15);
      setRegister (lhs.of_reg xmm_1) (mux (ugt v_3 (expression.bv_nat 64 31)) (expression.bv_nat 128 0) v_16);
      pure ()
     action
