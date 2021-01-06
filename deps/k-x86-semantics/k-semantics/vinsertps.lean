def vinsertps : instruction :=
  definst "vinsertps" $ do
    instr_pat $ fun (imm_0 : imm int) (mem_1 : Mem) (xmm_2 : reg (bv 128)) (xmm_3 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_4 <- eval (handleImmediateWithSignExtend imm_0 8 8);
      let (v_5 : expression (bv 2)) <- eval (extract v_4 2 4);
      let v_6 <- eval (eq v_5 (expression.bv_nat 2 0));
      let v_7 <- getRegister (lhs.of_reg xmm_2);
      let (v_8 : expression (bv 32)) <- eval (extract v_7 0 32);
      let v_9 <- eval (eq v_5 (expression.bv_nat 2 1));
      let v_10 <- eval (eq v_5 (expression.bv_nat 2 2));
      let v_11 <- evaluateAddress mem_1;
      let v_12 <- load v_11 4;
      let (v_13 : expression (bv 32)) <- eval (extract v_7 32 64);
      let v_14 <- eval (concat (mux (isBitSet v_4 4) (expression.bv_nat 32 0) (mux v_6 v_8 (mux v_9 v_8 (mux v_10 v_8 v_12)))) (mux (isBitSet v_4 5) (expression.bv_nat 32 0) (mux v_6 v_13 (mux v_9 v_13 (mux v_10 v_12 v_13)))));
      let (v_15 : expression (bv 32)) <- eval (extract v_7 64 96);
      let v_16 <- eval (concat v_14 (mux (isBitSet v_4 6) (expression.bv_nat 32 0) (mux v_6 v_15 (mux v_9 v_12 v_15))));
      let (v_17 : expression (bv 32)) <- eval (extract v_7 96 128);
      let v_18 <- eval (concat v_16 (mux (isBitSet v_4 7) (expression.bv_nat 32 0) (mux v_6 v_12 v_17)));
      setRegister (lhs.of_reg xmm_3) v_18;
      pure ()
     action;
    instr_pat $ fun (imm_0 : imm int) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) (xmm_3 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_4 <- eval (handleImmediateWithSignExtend imm_0 8 8);
      let (v_5 : expression (bv 2)) <- eval (extract v_4 2 4);
      let v_6 <- eval (eq v_5 (expression.bv_nat 2 0));
      let v_7 <- getRegister (lhs.of_reg xmm_2);
      let (v_8 : expression (bv 32)) <- eval (extract v_7 0 32);
      let v_9 <- eval (eq v_5 (expression.bv_nat 2 1));
      let v_10 <- eval (eq v_5 (expression.bv_nat 2 2));
      let (v_11 : expression (bv 2)) <- eval (extract v_4 0 2);
      let v_12 <- getRegister (lhs.of_reg xmm_1);
      let (v_13 : expression (bv 32)) <- eval (extract v_12 96 128);
      let (v_14 : expression (bv 32)) <- eval (extract v_12 64 96);
      let (v_15 : expression (bv 32)) <- eval (extract v_12 32 64);
      let (v_16 : expression (bv 32)) <- eval (extract v_12 0 32);
      let v_17 <- eval (mux (eq v_11 (expression.bv_nat 2 0)) v_13 (mux (eq v_11 (expression.bv_nat 2 1)) v_14 (mux (eq v_11 (expression.bv_nat 2 2)) v_15 v_16)));
      let (v_18 : expression (bv 32)) <- eval (extract v_7 32 64);
      let v_19 <- eval (concat (mux (isBitSet v_4 4) (expression.bv_nat 32 0) (mux v_6 v_8 (mux v_9 v_8 (mux v_10 v_8 v_17)))) (mux (isBitSet v_4 5) (expression.bv_nat 32 0) (mux v_6 v_18 (mux v_9 v_18 (mux v_10 v_17 v_18)))));
      let (v_20 : expression (bv 32)) <- eval (extract v_7 64 96);
      let v_21 <- eval (concat v_19 (mux (isBitSet v_4 6) (expression.bv_nat 32 0) (mux v_6 v_20 (mux v_9 v_17 v_20))));
      let (v_22 : expression (bv 32)) <- eval (extract v_7 96 128);
      let v_23 <- eval (concat v_21 (mux (isBitSet v_4 7) (expression.bv_nat 32 0) (mux v_6 v_17 v_22)));
      setRegister (lhs.of_reg xmm_3) v_23;
      pure ()
     action
