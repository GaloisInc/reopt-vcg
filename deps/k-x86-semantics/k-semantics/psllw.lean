def psllw : instruction :=
  definst "psllw" $ do
    instr_pat $ fun (imm_0 : imm int) (xmm_1 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_2 <- eval (handleImmediateWithSignExtend imm_0 8 8);
      let v_3 <- eval (concat (expression.bv_nat 56 0) v_2);
      let v_4 <- getRegister (lhs.of_reg xmm_1);
      let (v_5 : expression (bv 16)) <- eval (extract v_4 0 16);
      let v_6 <- eval (concat (expression.bv_nat 8 0) v_2);
      let (v_7 : expression (bv 16)) <- eval (extract (shl v_5 v_6) 0 16);
      let (v_8 : expression (bv 16)) <- eval (extract v_4 16 32);
      let (v_9 : expression (bv 16)) <- eval (extract (shl v_8 v_6) 0 16);
      let (v_10 : expression (bv 16)) <- eval (extract v_4 32 48);
      let (v_11 : expression (bv 16)) <- eval (extract (shl v_10 v_6) 0 16);
      let (v_12 : expression (bv 16)) <- eval (extract v_4 48 64);
      let (v_13 : expression (bv 16)) <- eval (extract (shl v_12 v_6) 0 16);
      let (v_14 : expression (bv 16)) <- eval (extract v_4 64 80);
      let (v_15 : expression (bv 16)) <- eval (extract (shl v_14 v_6) 0 16);
      let (v_16 : expression (bv 16)) <- eval (extract v_4 80 96);
      let (v_17 : expression (bv 16)) <- eval (extract (shl v_16 v_6) 0 16);
      let (v_18 : expression (bv 16)) <- eval (extract v_4 96 112);
      let (v_19 : expression (bv 16)) <- eval (extract (shl v_18 v_6) 0 16);
      let (v_20 : expression (bv 16)) <- eval (extract v_4 112 128);
      let (v_21 : expression (bv 16)) <- eval (extract (shl v_20 v_6) 0 16);
      let v_22 <- eval (concat v_19 v_21);
      let v_23 <- eval (concat v_17 v_22);
      let v_24 <- eval (concat v_15 v_23);
      let v_25 <- eval (concat v_13 v_24);
      let v_26 <- eval (concat v_11 v_25);
      let v_27 <- eval (concat v_9 v_26);
      let v_28 <- eval (concat v_7 v_27);
      setRegister (lhs.of_reg xmm_1) (mux (ugt v_3 (expression.bv_nat 64 15)) (expression.bv_nat 128 0) v_28);
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
      let (v_8 : expression (bv 16)) <- eval (extract (shl v_6 v_7) 0 16);
      let (v_9 : expression (bv 16)) <- eval (extract v_5 16 32);
      let (v_10 : expression (bv 16)) <- eval (extract (shl v_9 v_7) 0 16);
      let (v_11 : expression (bv 16)) <- eval (extract v_5 32 48);
      let (v_12 : expression (bv 16)) <- eval (extract (shl v_11 v_7) 0 16);
      let (v_13 : expression (bv 16)) <- eval (extract v_5 48 64);
      let (v_14 : expression (bv 16)) <- eval (extract (shl v_13 v_7) 0 16);
      let (v_15 : expression (bv 16)) <- eval (extract v_5 64 80);
      let (v_16 : expression (bv 16)) <- eval (extract (shl v_15 v_7) 0 16);
      let (v_17 : expression (bv 16)) <- eval (extract v_5 80 96);
      let (v_18 : expression (bv 16)) <- eval (extract (shl v_17 v_7) 0 16);
      let (v_19 : expression (bv 16)) <- eval (extract v_5 96 112);
      let (v_20 : expression (bv 16)) <- eval (extract (shl v_19 v_7) 0 16);
      let (v_21 : expression (bv 16)) <- eval (extract v_5 112 128);
      let (v_22 : expression (bv 16)) <- eval (extract (shl v_21 v_7) 0 16);
      let v_23 <- eval (concat v_20 v_22);
      let v_24 <- eval (concat v_18 v_23);
      let v_25 <- eval (concat v_16 v_24);
      let v_26 <- eval (concat v_14 v_25);
      let v_27 <- eval (concat v_12 v_26);
      let v_28 <- eval (concat v_10 v_27);
      let v_29 <- eval (concat v_8 v_28);
      setRegister (lhs.of_reg xmm_1) (mux (ugt v_4 (expression.bv_nat 64 15)) (expression.bv_nat 128 0) v_29);
      pure ()
     action;
    instr_pat $ fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_2 <- getRegister (lhs.of_reg xmm_0);
      let (v_3 : expression (bv 64)) <- eval (extract v_2 64 128);
      let v_4 <- getRegister (lhs.of_reg xmm_1);
      let (v_5 : expression (bv 16)) <- eval (extract v_4 0 16);
      let (v_6 : expression (bv 16)) <- eval (extract v_2 112 128);
      let (v_7 : expression (bv 16)) <- eval (extract (shl v_5 v_6) 0 16);
      let (v_8 : expression (bv 16)) <- eval (extract v_4 16 32);
      let (v_9 : expression (bv 16)) <- eval (extract (shl v_8 v_6) 0 16);
      let (v_10 : expression (bv 16)) <- eval (extract v_4 32 48);
      let (v_11 : expression (bv 16)) <- eval (extract (shl v_10 v_6) 0 16);
      let (v_12 : expression (bv 16)) <- eval (extract v_4 48 64);
      let (v_13 : expression (bv 16)) <- eval (extract (shl v_12 v_6) 0 16);
      let (v_14 : expression (bv 16)) <- eval (extract v_4 64 80);
      let (v_15 : expression (bv 16)) <- eval (extract (shl v_14 v_6) 0 16);
      let (v_16 : expression (bv 16)) <- eval (extract v_4 80 96);
      let (v_17 : expression (bv 16)) <- eval (extract (shl v_16 v_6) 0 16);
      let (v_18 : expression (bv 16)) <- eval (extract v_4 96 112);
      let (v_19 : expression (bv 16)) <- eval (extract (shl v_18 v_6) 0 16);
      let (v_20 : expression (bv 16)) <- eval (extract v_4 112 128);
      let (v_21 : expression (bv 16)) <- eval (extract (shl v_20 v_6) 0 16);
      let v_22 <- eval (concat v_19 v_21);
      let v_23 <- eval (concat v_17 v_22);
      let v_24 <- eval (concat v_15 v_23);
      let v_25 <- eval (concat v_13 v_24);
      let v_26 <- eval (concat v_11 v_25);
      let v_27 <- eval (concat v_9 v_26);
      let v_28 <- eval (concat v_7 v_27);
      setRegister (lhs.of_reg xmm_1) (mux (ugt v_3 (expression.bv_nat 64 15)) (expression.bv_nat 128 0) v_28);
      pure ()
     action
