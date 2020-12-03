def vpmovsxwd : instruction :=
  definst "vpmovsxwd" $ do
    instr_pat $ fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_2 <- evaluateAddress mem_0;
      let v_3 <- load v_2 8;
      let (v_4 : expression (bv 16)) <- eval (extract v_3 0 16);
      let (v_5 : expression (bv 16)) <- eval (extract v_3 16 32);
      let (v_6 : expression (bv 16)) <- eval (extract v_3 32 48);
      let (v_7 : expression (bv 16)) <- eval (extract v_3 48 64);
      let v_8 <- eval (concat (sext v_6 32) (sext v_7 32));
      let v_9 <- eval (concat (sext v_5 32) v_8);
      let v_10 <- eval (concat (sext v_4 32) v_9);
      setRegister (lhs.of_reg xmm_1) v_10;
      pure ()
     action;
    instr_pat $ fun (mem_0 : Mem) (ymm_1 : reg (bv 256)) =>
     let action : semantics Unit := do
      let v_2 <- evaluateAddress mem_0;
      let v_3 <- load v_2 16;
      let (v_4 : expression (bv 16)) <- eval (extract v_3 0 16);
      let (v_5 : expression (bv 16)) <- eval (extract v_3 16 32);
      let (v_6 : expression (bv 16)) <- eval (extract v_3 32 48);
      let (v_7 : expression (bv 16)) <- eval (extract v_3 48 64);
      let (v_8 : expression (bv 16)) <- eval (extract v_3 64 80);
      let (v_9 : expression (bv 16)) <- eval (extract v_3 80 96);
      let (v_10 : expression (bv 16)) <- eval (extract v_3 96 112);
      let (v_11 : expression (bv 16)) <- eval (extract v_3 112 128);
      let v_12 <- eval (concat (sext v_10 32) (sext v_11 32));
      let v_13 <- eval (concat (sext v_9 32) v_12);
      let v_14 <- eval (concat (sext v_8 32) v_13);
      let v_15 <- eval (concat (sext v_7 32) v_14);
      let v_16 <- eval (concat (sext v_6 32) v_15);
      let v_17 <- eval (concat (sext v_5 32) v_16);
      let v_18 <- eval (concat (sext v_4 32) v_17);
      setRegister (lhs.of_reg ymm_1) v_18;
      pure ()
     action;
    instr_pat $ fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_2 <- getRegister (lhs.of_reg xmm_0);
      let (v_3 : expression (bv 16)) <- eval (extract v_2 64 80);
      let (v_4 : expression (bv 16)) <- eval (extract v_2 80 96);
      let (v_5 : expression (bv 16)) <- eval (extract v_2 96 112);
      let (v_6 : expression (bv 16)) <- eval (extract v_2 112 128);
      let v_7 <- eval (concat (sext v_5 32) (sext v_6 32));
      let v_8 <- eval (concat (sext v_4 32) v_7);
      let v_9 <- eval (concat (sext v_3 32) v_8);
      setRegister (lhs.of_reg xmm_1) v_9;
      pure ()
     action;
    instr_pat $ fun (xmm_0 : reg (bv 128)) (ymm_1 : reg (bv 256)) =>
     let action : semantics Unit := do
      let v_2 <- getRegister (lhs.of_reg xmm_0);
      let (v_3 : expression (bv 16)) <- eval (extract v_2 0 16);
      let (v_4 : expression (bv 16)) <- eval (extract v_2 16 32);
      let (v_5 : expression (bv 16)) <- eval (extract v_2 32 48);
      let (v_6 : expression (bv 16)) <- eval (extract v_2 48 64);
      let (v_7 : expression (bv 16)) <- eval (extract v_2 64 80);
      let (v_8 : expression (bv 16)) <- eval (extract v_2 80 96);
      let (v_9 : expression (bv 16)) <- eval (extract v_2 96 112);
      let (v_10 : expression (bv 16)) <- eval (extract v_2 112 128);
      let v_11 <- eval (concat (sext v_9 32) (sext v_10 32));
      let v_12 <- eval (concat (sext v_8 32) v_11);
      let v_13 <- eval (concat (sext v_7 32) v_12);
      let v_14 <- eval (concat (sext v_6 32) v_13);
      let v_15 <- eval (concat (sext v_5 32) v_14);
      let v_16 <- eval (concat (sext v_4 32) v_15);
      let v_17 <- eval (concat (sext v_3 32) v_16);
      setRegister (lhs.of_reg ymm_1) v_17;
      pure ()
     action
