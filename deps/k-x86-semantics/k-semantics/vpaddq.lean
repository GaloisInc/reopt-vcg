def vpaddq : instruction :=
  definst "vpaddq" $ do
    instr_pat $ fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_3 <- getRegister (lhs.of_reg xmm_1);
      let (v_4 : expression (bv 64)) <- eval (extract v_3 0 64);
      let v_5 <- evaluateAddress mem_0;
      let v_6 <- load v_5 16;
      let (v_7 : expression (bv 64)) <- eval (extract v_6 0 64);
      let (v_8 : expression (bv 64)) <- eval (extract v_3 64 128);
      let (v_9 : expression (bv 64)) <- eval (extract v_6 64 128);
      let v_10 <- eval (concat (add v_4 v_7) (add v_8 v_9));
      setRegister (lhs.of_reg xmm_2) v_10;
      pure ()
     action;
    instr_pat $ fun (mem_0 : Mem) (ymm_1 : reg (bv 256)) (ymm_2 : reg (bv 256)) =>
     let action : semantics Unit := do
      let v_3 <- getRegister (lhs.of_reg ymm_1);
      let (v_4 : expression (bv 64)) <- eval (extract v_3 0 64);
      let v_5 <- evaluateAddress mem_0;
      let v_6 <- load v_5 32;
      let (v_7 : expression (bv 64)) <- eval (extract v_6 0 64);
      let (v_8 : expression (bv 64)) <- eval (extract v_3 64 128);
      let (v_9 : expression (bv 64)) <- eval (extract v_6 64 128);
      let (v_10 : expression (bv 64)) <- eval (extract v_3 128 192);
      let (v_11 : expression (bv 64)) <- eval (extract v_6 128 192);
      let (v_12 : expression (bv 64)) <- eval (extract v_3 192 256);
      let (v_13 : expression (bv 64)) <- eval (extract v_6 192 256);
      let v_14 <- eval (concat (add v_10 v_11) (add v_12 v_13));
      let v_15 <- eval (concat (add v_8 v_9) v_14);
      let v_16 <- eval (concat (add v_4 v_7) v_15);
      setRegister (lhs.of_reg ymm_2) v_16;
      pure ()
     action;
    instr_pat $ fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_3 <- getRegister (lhs.of_reg xmm_1);
      let (v_4 : expression (bv 64)) <- eval (extract v_3 0 64);
      let v_5 <- getRegister (lhs.of_reg xmm_0);
      let (v_6 : expression (bv 64)) <- eval (extract v_5 0 64);
      let (v_7 : expression (bv 64)) <- eval (extract v_3 64 128);
      let (v_8 : expression (bv 64)) <- eval (extract v_5 64 128);
      let v_9 <- eval (concat (add v_4 v_6) (add v_7 v_8));
      setRegister (lhs.of_reg xmm_2) v_9;
      pure ()
     action;
    instr_pat $ fun (ymm_0 : reg (bv 256)) (ymm_1 : reg (bv 256)) (ymm_2 : reg (bv 256)) =>
     let action : semantics Unit := do
      let v_3 <- getRegister (lhs.of_reg ymm_1);
      let (v_4 : expression (bv 64)) <- eval (extract v_3 0 64);
      let v_5 <- getRegister (lhs.of_reg ymm_0);
      let (v_6 : expression (bv 64)) <- eval (extract v_5 0 64);
      let (v_7 : expression (bv 64)) <- eval (extract v_3 64 128);
      let (v_8 : expression (bv 64)) <- eval (extract v_5 64 128);
      let (v_9 : expression (bv 64)) <- eval (extract v_3 128 192);
      let (v_10 : expression (bv 64)) <- eval (extract v_5 128 192);
      let (v_11 : expression (bv 64)) <- eval (extract v_3 192 256);
      let (v_12 : expression (bv 64)) <- eval (extract v_5 192 256);
      let v_13 <- eval (concat (add v_9 v_10) (add v_11 v_12));
      let v_14 <- eval (concat (add v_7 v_8) v_13);
      let v_15 <- eval (concat (add v_4 v_6) v_14);
      setRegister (lhs.of_reg ymm_2) v_15;
      pure ()
     action
