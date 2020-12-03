def pblendw : instruction :=
  definst "pblendw" $ do
    instr_pat $ fun (imm_0 : imm int) (mem_1 : Mem) (xmm_2 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_3 <- eval (handleImmediateWithSignExtend imm_0 8 8);
      let v_4 <- getRegister (lhs.of_reg xmm_2);
      let (v_5 : expression (bv 16)) <- eval (extract v_4 0 16);
      let v_6 <- evaluateAddress mem_1;
      let v_7 <- load v_6 16;
      let (v_8 : expression (bv 16)) <- eval (extract v_7 0 16);
      let (v_9 : expression (bv 16)) <- eval (extract v_4 16 32);
      let (v_10 : expression (bv 16)) <- eval (extract v_7 16 32);
      let (v_11 : expression (bv 16)) <- eval (extract v_4 32 48);
      let (v_12 : expression (bv 16)) <- eval (extract v_7 32 48);
      let (v_13 : expression (bv 16)) <- eval (extract v_4 48 64);
      let (v_14 : expression (bv 16)) <- eval (extract v_7 48 64);
      let (v_15 : expression (bv 16)) <- eval (extract v_4 64 80);
      let (v_16 : expression (bv 16)) <- eval (extract v_7 64 80);
      let (v_17 : expression (bv 16)) <- eval (extract v_4 80 96);
      let (v_18 : expression (bv 16)) <- eval (extract v_7 80 96);
      let (v_19 : expression (bv 16)) <- eval (extract v_4 96 112);
      let (v_20 : expression (bv 16)) <- eval (extract v_7 96 112);
      let (v_21 : expression (bv 16)) <- eval (extract v_4 112 128);
      let (v_22 : expression (bv 16)) <- eval (extract v_7 112 128);
      let v_23 <- eval (concat (mux (isBitClear v_3 6) v_19 v_20) (mux (isBitClear v_3 7) v_21 v_22));
      let v_24 <- eval (concat (mux (isBitClear v_3 5) v_17 v_18) v_23);
      let v_25 <- eval (concat (mux (isBitClear v_3 4) v_15 v_16) v_24);
      let v_26 <- eval (concat (mux (isBitClear v_3 3) v_13 v_14) v_25);
      let v_27 <- eval (concat (mux (isBitClear v_3 2) v_11 v_12) v_26);
      let v_28 <- eval (concat (mux (isBitClear v_3 1) v_9 v_10) v_27);
      let v_29 <- eval (concat (mux (isBitClear v_3 0) v_5 v_8) v_28);
      setRegister (lhs.of_reg xmm_2) v_29;
      pure ()
     action;
    instr_pat $ fun (imm_0 : imm int) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_3 <- eval (handleImmediateWithSignExtend imm_0 8 8);
      let v_4 <- getRegister (lhs.of_reg xmm_2);
      let (v_5 : expression (bv 16)) <- eval (extract v_4 0 16);
      let v_6 <- getRegister (lhs.of_reg xmm_1);
      let (v_7 : expression (bv 16)) <- eval (extract v_6 0 16);
      let (v_8 : expression (bv 16)) <- eval (extract v_4 16 32);
      let (v_9 : expression (bv 16)) <- eval (extract v_6 16 32);
      let (v_10 : expression (bv 16)) <- eval (extract v_4 32 48);
      let (v_11 : expression (bv 16)) <- eval (extract v_6 32 48);
      let (v_12 : expression (bv 16)) <- eval (extract v_4 48 64);
      let (v_13 : expression (bv 16)) <- eval (extract v_6 48 64);
      let (v_14 : expression (bv 16)) <- eval (extract v_4 64 80);
      let (v_15 : expression (bv 16)) <- eval (extract v_6 64 80);
      let (v_16 : expression (bv 16)) <- eval (extract v_4 80 96);
      let (v_17 : expression (bv 16)) <- eval (extract v_6 80 96);
      let (v_18 : expression (bv 16)) <- eval (extract v_4 96 112);
      let (v_19 : expression (bv 16)) <- eval (extract v_6 96 112);
      let (v_20 : expression (bv 16)) <- eval (extract v_4 112 128);
      let (v_21 : expression (bv 16)) <- eval (extract v_6 112 128);
      let v_22 <- eval (concat (mux (isBitClear v_3 6) v_18 v_19) (mux (isBitClear v_3 7) v_20 v_21));
      let v_23 <- eval (concat (mux (isBitClear v_3 5) v_16 v_17) v_22);
      let v_24 <- eval (concat (mux (isBitClear v_3 4) v_14 v_15) v_23);
      let v_25 <- eval (concat (mux (isBitClear v_3 3) v_12 v_13) v_24);
      let v_26 <- eval (concat (mux (isBitClear v_3 2) v_10 v_11) v_25);
      let v_27 <- eval (concat (mux (isBitClear v_3 1) v_8 v_9) v_26);
      let v_28 <- eval (concat (mux (isBitClear v_3 0) v_5 v_7) v_27);
      setRegister (lhs.of_reg xmm_2) v_28;
      pure ()
     action
