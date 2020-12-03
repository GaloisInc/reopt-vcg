def pshufhw : instruction :=
  definst "pshufhw" $ do
    instr_pat $ fun (imm_0 : imm int) (mem_1 : Mem) (xmm_2 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_3 <- evaluateAddress mem_1;
      let v_4 <- load v_3 16;
      let v_5 <- eval (handleImmediateWithSignExtend imm_0 8 8);
      let (v_6 : expression (bv 2)) <- eval (extract v_5 0 2);
      let v_7 <- eval (concat (expression.bv_nat 126 0) v_6);
      let (v_8 : expression (bv 128)) <- eval (extract (shl v_7 (expression.bv_nat 128 4)) 0 128);
      let (v_9 : expression (bv 16)) <- eval (extract (lshr v_4 v_8) 48 64);
      let (v_10 : expression (bv 2)) <- eval (extract v_5 2 4);
      let v_11 <- eval (concat (expression.bv_nat 126 0) v_10);
      let (v_12 : expression (bv 128)) <- eval (extract (shl v_11 (expression.bv_nat 128 4)) 0 128);
      let (v_13 : expression (bv 16)) <- eval (extract (lshr v_4 v_12) 48 64);
      let (v_14 : expression (bv 2)) <- eval (extract v_5 4 6);
      let v_15 <- eval (concat (expression.bv_nat 126 0) v_14);
      let (v_16 : expression (bv 128)) <- eval (extract (shl v_15 (expression.bv_nat 128 4)) 0 128);
      let (v_17 : expression (bv 16)) <- eval (extract (lshr v_4 v_16) 48 64);
      let (v_18 : expression (bv 2)) <- eval (extract v_5 6 8);
      let v_19 <- eval (concat (expression.bv_nat 126 0) v_18);
      let (v_20 : expression (bv 128)) <- eval (extract (shl v_19 (expression.bv_nat 128 4)) 0 128);
      let (v_21 : expression (bv 16)) <- eval (extract (lshr v_4 v_20) 48 64);
      let (v_22 : expression (bv 64)) <- eval (extract v_4 64 128);
      let v_23 <- eval (concat v_21 v_22);
      let v_24 <- eval (concat v_17 v_23);
      let v_25 <- eval (concat v_13 v_24);
      let v_26 <- eval (concat v_9 v_25);
      setRegister (lhs.of_reg xmm_2) v_26;
      pure ()
     action;
    instr_pat $ fun (imm_0 : imm int) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_3 <- getRegister (lhs.of_reg xmm_1);
      let v_4 <- eval (handleImmediateWithSignExtend imm_0 8 8);
      let (v_5 : expression (bv 2)) <- eval (extract v_4 0 2);
      let v_6 <- eval (concat (expression.bv_nat 126 0) v_5);
      let (v_7 : expression (bv 128)) <- eval (extract (shl v_6 (expression.bv_nat 128 4)) 0 128);
      let (v_8 : expression (bv 16)) <- eval (extract (lshr v_3 v_7) 48 64);
      let (v_9 : expression (bv 2)) <- eval (extract v_4 2 4);
      let v_10 <- eval (concat (expression.bv_nat 126 0) v_9);
      let (v_11 : expression (bv 128)) <- eval (extract (shl v_10 (expression.bv_nat 128 4)) 0 128);
      let (v_12 : expression (bv 16)) <- eval (extract (lshr v_3 v_11) 48 64);
      let (v_13 : expression (bv 2)) <- eval (extract v_4 4 6);
      let v_14 <- eval (concat (expression.bv_nat 126 0) v_13);
      let (v_15 : expression (bv 128)) <- eval (extract (shl v_14 (expression.bv_nat 128 4)) 0 128);
      let (v_16 : expression (bv 16)) <- eval (extract (lshr v_3 v_15) 48 64);
      let (v_17 : expression (bv 2)) <- eval (extract v_4 6 8);
      let v_18 <- eval (concat (expression.bv_nat 126 0) v_17);
      let (v_19 : expression (bv 128)) <- eval (extract (shl v_18 (expression.bv_nat 128 4)) 0 128);
      let (v_20 : expression (bv 16)) <- eval (extract (lshr v_3 v_19) 48 64);
      let (v_21 : expression (bv 64)) <- eval (extract v_3 64 128);
      let v_22 <- eval (concat v_20 v_21);
      let v_23 <- eval (concat v_16 v_22);
      let v_24 <- eval (concat v_12 v_23);
      let v_25 <- eval (concat v_8 v_24);
      setRegister (lhs.of_reg xmm_2) v_25;
      pure ()
     action
