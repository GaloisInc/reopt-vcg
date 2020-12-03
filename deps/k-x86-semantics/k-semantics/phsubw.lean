def phsubw : instruction :=
  definst "phsubw" $ do
    instr_pat $ fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_2 <- evaluateAddress mem_0;
      let v_3 <- load v_2 16;
      let (v_4 : expression (bv 16)) <- eval (extract v_3 16 32);
      let (v_5 : expression (bv 16)) <- eval (extract v_3 0 16);
      let (v_6 : expression (bv 16)) <- eval (extract v_3 48 64);
      let (v_7 : expression (bv 16)) <- eval (extract v_3 32 48);
      let v_8 <- eval (concat (sub v_4 v_5) (sub v_6 v_7));
      let (v_9 : expression (bv 16)) <- eval (extract v_3 80 96);
      let (v_10 : expression (bv 16)) <- eval (extract v_3 64 80);
      let v_11 <- eval (concat v_8 (sub v_9 v_10));
      let (v_12 : expression (bv 16)) <- eval (extract v_3 112 128);
      let (v_13 : expression (bv 16)) <- eval (extract v_3 96 112);
      let v_14 <- eval (concat v_11 (sub v_12 v_13));
      let v_15 <- getRegister (lhs.of_reg xmm_1);
      let (v_16 : expression (bv 16)) <- eval (extract v_15 16 32);
      let (v_17 : expression (bv 16)) <- eval (extract v_15 0 16);
      let v_18 <- eval (concat v_14 (sub v_16 v_17));
      let (v_19 : expression (bv 16)) <- eval (extract v_15 48 64);
      let (v_20 : expression (bv 16)) <- eval (extract v_15 32 48);
      let v_21 <- eval (concat v_18 (sub v_19 v_20));
      let (v_22 : expression (bv 16)) <- eval (extract v_15 80 96);
      let (v_23 : expression (bv 16)) <- eval (extract v_15 64 80);
      let v_24 <- eval (concat v_21 (sub v_22 v_23));
      let (v_25 : expression (bv 16)) <- eval (extract v_15 112 128);
      let (v_26 : expression (bv 16)) <- eval (extract v_15 96 112);
      let v_27 <- eval (concat v_24 (sub v_25 v_26));
      setRegister (lhs.of_reg xmm_1) v_27;
      pure ()
     action;
    instr_pat $ fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_2 <- getRegister (lhs.of_reg xmm_0);
      let (v_3 : expression (bv 16)) <- eval (extract v_2 16 32);
      let (v_4 : expression (bv 16)) <- eval (extract v_2 0 16);
      let (v_5 : expression (bv 16)) <- eval (extract v_2 48 64);
      let (v_6 : expression (bv 16)) <- eval (extract v_2 32 48);
      let v_7 <- eval (concat (sub v_3 v_4) (sub v_5 v_6));
      let (v_8 : expression (bv 16)) <- eval (extract v_2 80 96);
      let (v_9 : expression (bv 16)) <- eval (extract v_2 64 80);
      let v_10 <- eval (concat v_7 (sub v_8 v_9));
      let (v_11 : expression (bv 16)) <- eval (extract v_2 112 128);
      let (v_12 : expression (bv 16)) <- eval (extract v_2 96 112);
      let v_13 <- eval (concat v_10 (sub v_11 v_12));
      let v_14 <- getRegister (lhs.of_reg xmm_1);
      let (v_15 : expression (bv 16)) <- eval (extract v_14 16 32);
      let (v_16 : expression (bv 16)) <- eval (extract v_14 0 16);
      let v_17 <- eval (concat v_13 (sub v_15 v_16));
      let (v_18 : expression (bv 16)) <- eval (extract v_14 48 64);
      let (v_19 : expression (bv 16)) <- eval (extract v_14 32 48);
      let v_20 <- eval (concat v_17 (sub v_18 v_19));
      let (v_21 : expression (bv 16)) <- eval (extract v_14 80 96);
      let (v_22 : expression (bv 16)) <- eval (extract v_14 64 80);
      let v_23 <- eval (concat v_20 (sub v_21 v_22));
      let (v_24 : expression (bv 16)) <- eval (extract v_14 112 128);
      let (v_25 : expression (bv 16)) <- eval (extract v_14 96 112);
      let v_26 <- eval (concat v_23 (sub v_24 v_25));
      setRegister (lhs.of_reg xmm_1) v_26;
      pure ()
     action
