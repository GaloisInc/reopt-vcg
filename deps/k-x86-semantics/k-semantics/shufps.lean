def shufps : instruction :=
  definst "shufps" $ do
    instr_pat $ fun (imm_0 : imm int) (mem_1 : Mem) (xmm_2 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_3 <- eval (handleImmediateWithSignExtend imm_0 8 8);
      let v_4 <- eval (isBitSet v_3 0);
      let v_5 <- evaluateAddress mem_1;
      let v_6 <- load v_5 16;
      let (v_7 : expression (bv 32)) <- eval (extract v_6 0 32);
      let (v_8 : expression (bv 32)) <- eval (extract v_6 64 96);
      let (v_9 : expression (bv 32)) <- eval (extract v_6 32 64);
      let (v_10 : expression (bv 32)) <- eval (extract v_6 96 128);
      let v_11 <- eval (isBitSet v_3 2);
      let v_12 <- eval (isBitSet v_3 4);
      let v_13 <- getRegister (lhs.of_reg xmm_2);
      let (v_14 : expression (bv 32)) <- eval (extract v_13 0 32);
      let (v_15 : expression (bv 32)) <- eval (extract v_13 64 96);
      let (v_16 : expression (bv 32)) <- eval (extract v_13 32 64);
      let (v_17 : expression (bv 32)) <- eval (extract v_13 96 128);
      let v_18 <- eval (isBitSet v_3 6);
      let v_19 <- eval (concat (mux (isBitSet v_3 5) (mux v_12 v_14 v_15) (mux v_12 v_16 v_17)) (mux (isBitSet v_3 7) (mux v_18 v_14 v_15) (mux v_18 v_16 v_17)));
      let v_20 <- eval (concat (mux (isBitSet v_3 3) (mux v_11 v_7 v_8) (mux v_11 v_9 v_10)) v_19);
      let v_21 <- eval (concat (mux (isBitSet v_3 1) (mux v_4 v_7 v_8) (mux v_4 v_9 v_10)) v_20);
      setRegister (lhs.of_reg xmm_2) v_21;
      pure ()
     action;
    instr_pat $ fun (imm_0 : imm int) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_3 <- eval (handleImmediateWithSignExtend imm_0 8 8);
      let v_4 <- eval (isBitSet v_3 0);
      let v_5 <- getRegister (lhs.of_reg xmm_1);
      let (v_6 : expression (bv 32)) <- eval (extract v_5 0 32);
      let (v_7 : expression (bv 32)) <- eval (extract v_5 64 96);
      let (v_8 : expression (bv 32)) <- eval (extract v_5 32 64);
      let (v_9 : expression (bv 32)) <- eval (extract v_5 96 128);
      let v_10 <- eval (isBitSet v_3 2);
      let v_11 <- eval (isBitSet v_3 4);
      let v_12 <- getRegister (lhs.of_reg xmm_2);
      let (v_13 : expression (bv 32)) <- eval (extract v_12 0 32);
      let (v_14 : expression (bv 32)) <- eval (extract v_12 64 96);
      let (v_15 : expression (bv 32)) <- eval (extract v_12 32 64);
      let (v_16 : expression (bv 32)) <- eval (extract v_12 96 128);
      let v_17 <- eval (isBitSet v_3 6);
      let v_18 <- eval (concat (mux (isBitSet v_3 5) (mux v_11 v_13 v_14) (mux v_11 v_15 v_16)) (mux (isBitSet v_3 7) (mux v_17 v_13 v_14) (mux v_17 v_15 v_16)));
      let v_19 <- eval (concat (mux (isBitSet v_3 3) (mux v_10 v_6 v_7) (mux v_10 v_8 v_9)) v_18);
      let v_20 <- eval (concat (mux (isBitSet v_3 1) (mux v_4 v_6 v_7) (mux v_4 v_8 v_9)) v_19);
      setRegister (lhs.of_reg xmm_2) v_20;
      pure ()
     action
