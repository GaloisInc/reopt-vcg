def blendps : instruction :=
  definst "blendps" $ do
    instr_pat $ fun (imm_0 : imm int) (mem_1 : Mem) (xmm_2 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_3 <- eval (handleImmediateWithSignExtend imm_0 8 8);
      let v_4 <- getRegister (lhs.of_reg xmm_2);
      let (v_5 : expression (bv 32)) <- eval (extract v_4 0 32);
      let v_6 <- evaluateAddress mem_1;
      let v_7 <- load v_6 16;
      let (v_8 : expression (bv 32)) <- eval (extract v_7 0 32);
      let (v_9 : expression (bv 32)) <- eval (extract v_4 32 64);
      let (v_10 : expression (bv 32)) <- eval (extract v_7 32 64);
      let (v_11 : expression (bv 32)) <- eval (extract v_4 64 96);
      let (v_12 : expression (bv 32)) <- eval (extract v_7 64 96);
      let (v_13 : expression (bv 32)) <- eval (extract v_4 96 128);
      let (v_14 : expression (bv 32)) <- eval (extract v_7 96 128);
      let v_15 <- eval (concat (mux (isBitClear v_3 6) v_11 v_12) (mux (isBitClear v_3 7) v_13 v_14));
      let v_16 <- eval (concat (mux (isBitClear v_3 5) v_9 v_10) v_15);
      let v_17 <- eval (concat (mux (isBitClear v_3 4) v_5 v_8) v_16);
      setRegister (lhs.of_reg xmm_2) v_17;
      pure ()
     action;
    instr_pat $ fun (imm_0 : imm int) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_3 <- eval (handleImmediateWithSignExtend imm_0 8 8);
      let v_4 <- getRegister (lhs.of_reg xmm_2);
      let (v_5 : expression (bv 32)) <- eval (extract v_4 0 32);
      let v_6 <- getRegister (lhs.of_reg xmm_1);
      let (v_7 : expression (bv 32)) <- eval (extract v_6 0 32);
      let (v_8 : expression (bv 32)) <- eval (extract v_4 32 64);
      let (v_9 : expression (bv 32)) <- eval (extract v_6 32 64);
      let (v_10 : expression (bv 32)) <- eval (extract v_4 64 96);
      let (v_11 : expression (bv 32)) <- eval (extract v_6 64 96);
      let (v_12 : expression (bv 32)) <- eval (extract v_4 96 128);
      let (v_13 : expression (bv 32)) <- eval (extract v_6 96 128);
      let v_14 <- eval (concat (mux (isBitClear v_3 6) v_10 v_11) (mux (isBitClear v_3 7) v_12 v_13));
      let v_15 <- eval (concat (mux (isBitClear v_3 5) v_8 v_9) v_14);
      let v_16 <- eval (concat (mux (isBitClear v_3 4) v_5 v_7) v_15);
      setRegister (lhs.of_reg xmm_2) v_16;
      pure ()
     action
