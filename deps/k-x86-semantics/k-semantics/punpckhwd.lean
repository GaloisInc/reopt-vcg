def punpckhwd : instruction :=
  definst "punpckhwd" $ do
    instr_pat $ fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_2 <- evaluateAddress mem_0;
      let v_3 <- load v_2 16;
      let (v_4 : expression (bv 16)) <- eval (extract v_3 0 16);
      let v_5 <- getRegister (lhs.of_reg xmm_1);
      let (v_6 : expression (bv 16)) <- eval (extract v_5 0 16);
      let v_7 <- eval (concat v_4 v_6);
      let (v_8 : expression (bv 16)) <- eval (extract v_3 16 32);
      let (v_9 : expression (bv 16)) <- eval (extract v_5 16 32);
      let v_10 <- eval (concat v_8 v_9);
      let (v_11 : expression (bv 16)) <- eval (extract v_3 32 48);
      let (v_12 : expression (bv 16)) <- eval (extract v_5 32 48);
      let v_13 <- eval (concat v_11 v_12);
      let (v_14 : expression (bv 16)) <- eval (extract v_3 48 64);
      let (v_15 : expression (bv 16)) <- eval (extract v_5 48 64);
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
      let (v_3 : expression (bv 16)) <- eval (extract v_2 0 16);
      let v_4 <- getRegister (lhs.of_reg xmm_1);
      let (v_5 : expression (bv 16)) <- eval (extract v_4 0 16);
      let v_6 <- eval (concat v_3 v_5);
      let (v_7 : expression (bv 16)) <- eval (extract v_2 16 32);
      let (v_8 : expression (bv 16)) <- eval (extract v_4 16 32);
      let v_9 <- eval (concat v_7 v_8);
      let (v_10 : expression (bv 16)) <- eval (extract v_2 32 48);
      let (v_11 : expression (bv 16)) <- eval (extract v_4 32 48);
      let v_12 <- eval (concat v_10 v_11);
      let (v_13 : expression (bv 16)) <- eval (extract v_2 48 64);
      let (v_14 : expression (bv 16)) <- eval (extract v_4 48 64);
      let v_15 <- eval (concat v_13 v_14);
      let v_16 <- eval (concat v_12 v_15);
      let v_17 <- eval (concat v_9 v_16);
      let v_18 <- eval (concat v_6 v_17);
      setRegister (lhs.of_reg xmm_1) v_18;
      pure ()
     action
