def punpcklwd : instruction :=
  definst "punpcklwd" $ do
    instr_pat $ fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_2 <- evaluateAddress mem_0;
      let v_3 <- load v_2 16;
      let (v_4 : expression (bv 16)) <- eval (extract v_3 64 80);
      let v_5 <- getRegister (lhs.of_reg xmm_1);
      let (v_6 : expression (bv 16)) <- eval (extract v_5 64 80);
      let v_7 <- eval (concat v_4 v_6);
      let (v_8 : expression (bv 16)) <- eval (extract v_3 80 96);
      let (v_9 : expression (bv 16)) <- eval (extract v_5 80 96);
      let v_10 <- eval (concat v_8 v_9);
      let (v_11 : expression (bv 16)) <- eval (extract v_3 96 112);
      let (v_12 : expression (bv 16)) <- eval (extract v_5 96 112);
      let v_13 <- eval (concat v_11 v_12);
      let (v_14 : expression (bv 16)) <- eval (extract v_3 112 128);
      let (v_15 : expression (bv 16)) <- eval (extract v_5 112 128);
      let v_16 <- eval (concat v_14 v_15);
      let v_17 <- eval (concat v_13 v_16);
      let v_18 <- eval (concat v_10 v_17);
      let v_19 <- eval (concat v_7 v_18);
      setRegister (lhs.of_reg xmm_1) v_19;
      pure ()
     action;
    instr_pat $ fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_2 <- getRegister (lhs.of_reg xmm_0);
      let (v_3 : expression (bv 16)) <- eval (extract v_2 64 80);
      let v_4 <- getRegister (lhs.of_reg xmm_1);
      let (v_5 : expression (bv 16)) <- eval (extract v_4 64 80);
      let v_6 <- eval (concat v_3 v_5);
      let (v_7 : expression (bv 16)) <- eval (extract v_2 80 96);
      let (v_8 : expression (bv 16)) <- eval (extract v_4 80 96);
      let v_9 <- eval (concat v_7 v_8);
      let (v_10 : expression (bv 16)) <- eval (extract v_2 96 112);
      let (v_11 : expression (bv 16)) <- eval (extract v_4 96 112);
      let v_12 <- eval (concat v_10 v_11);
      let (v_13 : expression (bv 16)) <- eval (extract v_2 112 128);
      let (v_14 : expression (bv 16)) <- eval (extract v_4 112 128);
      let v_15 <- eval (concat v_13 v_14);
      let v_16 <- eval (concat v_12 v_15);
      let v_17 <- eval (concat v_9 v_16);
      let v_18 <- eval (concat v_6 v_17);
      setRegister (lhs.of_reg xmm_1) v_18;
      pure ()
     action
