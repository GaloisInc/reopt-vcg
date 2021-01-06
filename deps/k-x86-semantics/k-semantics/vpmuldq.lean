def vpmuldq : instruction :=
  definst "vpmuldq" $ do
    instr_pat $ fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_3 <- getRegister (lhs.of_reg xmm_1);
      let (v_4 : expression (bv 32)) <- eval (extract v_3 32 64);
      let v_5 <- evaluateAddress mem_0;
      let v_6 <- load v_5 16;
      let (v_7 : expression (bv 32)) <- eval (extract v_6 32 64);
      let (v_8 : expression (bv 32)) <- eval (extract v_3 96 128);
      let (v_9 : expression (bv 32)) <- eval (extract v_6 96 128);
      let v_10 <- eval (concat (mul (sext v_4 64) (sext v_7 64)) (mul (sext v_8 64) (sext v_9 64)));
      setRegister (lhs.of_reg xmm_2) v_10;
      pure ()
     action;
    instr_pat $ fun (mem_0 : Mem) (ymm_1 : reg (bv 256)) (ymm_2 : reg (bv 256)) =>
     let action : semantics Unit := do
      let v_3 <- getRegister (lhs.of_reg ymm_1);
      let (v_4 : expression (bv 32)) <- eval (extract v_3 32 64);
      let v_5 <- evaluateAddress mem_0;
      let v_6 <- load v_5 32;
      let (v_7 : expression (bv 32)) <- eval (extract v_6 32 64);
      let (v_8 : expression (bv 32)) <- eval (extract v_3 96 128);
      let (v_9 : expression (bv 32)) <- eval (extract v_6 96 128);
      let (v_10 : expression (bv 32)) <- eval (extract v_3 160 192);
      let (v_11 : expression (bv 32)) <- eval (extract v_6 160 192);
      let (v_12 : expression (bv 32)) <- eval (extract v_3 224 256);
      let (v_13 : expression (bv 32)) <- eval (extract v_6 224 256);
      let v_14 <- eval (concat (mul (sext v_10 64) (sext v_11 64)) (mul (sext v_12 64) (sext v_13 64)));
      let v_15 <- eval (concat (mul (sext v_8 64) (sext v_9 64)) v_14);
      let v_16 <- eval (concat (mul (sext v_4 64) (sext v_7 64)) v_15);
      setRegister (lhs.of_reg ymm_2) v_16;
      pure ()
     action;
    instr_pat $ fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_3 <- getRegister (lhs.of_reg xmm_1);
      let (v_4 : expression (bv 32)) <- eval (extract v_3 32 64);
      let v_5 <- getRegister (lhs.of_reg xmm_0);
      let (v_6 : expression (bv 32)) <- eval (extract v_5 32 64);
      let (v_7 : expression (bv 32)) <- eval (extract v_3 96 128);
      let (v_8 : expression (bv 32)) <- eval (extract v_5 96 128);
      let v_9 <- eval (concat (mul (sext v_4 64) (sext v_6 64)) (mul (sext v_7 64) (sext v_8 64)));
      setRegister (lhs.of_reg xmm_2) v_9;
      pure ()
     action;
    instr_pat $ fun (ymm_0 : reg (bv 256)) (ymm_1 : reg (bv 256)) (ymm_2 : reg (bv 256)) =>
     let action : semantics Unit := do
      let v_3 <- getRegister (lhs.of_reg ymm_1);
      let (v_4 : expression (bv 32)) <- eval (extract v_3 32 64);
      let v_5 <- getRegister (lhs.of_reg ymm_0);
      let (v_6 : expression (bv 32)) <- eval (extract v_5 32 64);
      let (v_7 : expression (bv 32)) <- eval (extract v_3 96 128);
      let (v_8 : expression (bv 32)) <- eval (extract v_5 96 128);
      let (v_9 : expression (bv 32)) <- eval (extract v_3 160 192);
      let (v_10 : expression (bv 32)) <- eval (extract v_5 160 192);
      let (v_11 : expression (bv 32)) <- eval (extract v_3 224 256);
      let (v_12 : expression (bv 32)) <- eval (extract v_5 224 256);
      let v_13 <- eval (concat (mul (sext v_9 64) (sext v_10 64)) (mul (sext v_11 64) (sext v_12 64)));
      let v_14 <- eval (concat (mul (sext v_7 64) (sext v_8 64)) v_13);
      let v_15 <- eval (concat (mul (sext v_4 64) (sext v_6 64)) v_14);
      setRegister (lhs.of_reg ymm_2) v_15;
      pure ()
     action
