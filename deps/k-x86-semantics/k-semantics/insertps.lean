def insertps : instruction :=
  definst "insertps" $ do
    instr_pat $ fun (imm_0 : imm int) (mem_1 : Mem) (xmm_2 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_3 <- eval (handleImmediateWithSignExtend imm_0 8 8);
      let (v_4 : expression (bv 2)) <- eval (extract v_3 2 4);
      let v_5 <- eval (eq v_4 (expression.bv_nat 2 0));
      let v_6 <- getRegister (lhs.of_reg xmm_2);
      let (v_7 : expression (bv 32)) <- eval (extract v_6 0 32);
      let v_8 <- eval (eq v_4 (expression.bv_nat 2 1));
      let v_9 <- eval (eq v_4 (expression.bv_nat 2 2));
      let v_10 <- evaluateAddress mem_1;
      let v_11 <- load v_10 4;
      let (v_12 : expression (bv 32)) <- eval (extract v_6 32 64);
      let v_13 <- eval (concat (mux (isBitSet v_3 4) (expression.bv_nat 32 0) (mux v_5 v_7 (mux v_8 v_7 (mux v_9 v_7 v_11)))) (mux (isBitSet v_3 5) (expression.bv_nat 32 0) (mux v_5 v_12 (mux v_8 v_12 (mux v_9 v_11 v_12)))));
      let (v_14 : expression (bv 32)) <- eval (extract v_6 64 96);
      let v_15 <- eval (concat v_13 (mux (isBitSet v_3 6) (expression.bv_nat 32 0) (mux v_5 v_14 (mux v_8 v_11 v_14))));
      let (v_16 : expression (bv 32)) <- eval (extract v_6 96 128);
      let v_17 <- eval (concat v_15 (mux (isBitSet v_3 7) (expression.bv_nat 32 0) (mux v_5 v_11 v_16)));
      setRegister (lhs.of_reg xmm_2) v_17;
      pure ()
     action;
    instr_pat $ fun (imm_0 : imm int) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_3 <- eval (handleImmediateWithSignExtend imm_0 8 8);
      let (v_4 : expression (bv 2)) <- eval (extract v_3 2 4);
      let v_5 <- eval (eq v_4 (expression.bv_nat 2 0));
      let v_6 <- getRegister (lhs.of_reg xmm_2);
      let (v_7 : expression (bv 32)) <- eval (extract v_6 0 32);
      let v_8 <- eval (eq v_4 (expression.bv_nat 2 1));
      let v_9 <- eval (eq v_4 (expression.bv_nat 2 2));
      let (v_10 : expression (bv 2)) <- eval (extract v_3 0 2);
      let v_11 <- getRegister (lhs.of_reg xmm_1);
      let (v_12 : expression (bv 32)) <- eval (extract v_11 96 128);
      let (v_13 : expression (bv 32)) <- eval (extract v_11 64 96);
      let (v_14 : expression (bv 32)) <- eval (extract v_11 32 64);
      let (v_15 : expression (bv 32)) <- eval (extract v_11 0 32);
      let v_16 <- eval (mux (eq v_10 (expression.bv_nat 2 0)) v_12 (mux (eq v_10 (expression.bv_nat 2 1)) v_13 (mux (eq v_10 (expression.bv_nat 2 2)) v_14 v_15)));
      let (v_17 : expression (bv 32)) <- eval (extract v_6 32 64);
      let v_18 <- eval (concat (mux (isBitSet v_3 4) (expression.bv_nat 32 0) (mux v_5 v_7 (mux v_8 v_7 (mux v_9 v_7 v_16)))) (mux (isBitSet v_3 5) (expression.bv_nat 32 0) (mux v_5 v_17 (mux v_8 v_17 (mux v_9 v_16 v_17)))));
      let (v_19 : expression (bv 32)) <- eval (extract v_6 64 96);
      let v_20 <- eval (concat v_18 (mux (isBitSet v_3 6) (expression.bv_nat 32 0) (mux v_5 v_19 (mux v_8 v_16 v_19))));
      let (v_21 : expression (bv 32)) <- eval (extract v_6 96 128);
      let v_22 <- eval (concat v_20 (mux (isBitSet v_3 7) (expression.bv_nat 32 0) (mux v_5 v_16 v_21)));
      setRegister (lhs.of_reg xmm_2) v_22;
      pure ()
     action
