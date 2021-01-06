def vpmuludq : instruction :=
  definst "vpmuludq" $ do
    instr_pat $ fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_3 <- getRegister (lhs.of_reg xmm_1);
      let (v_4 : expression (bv 32)) <- eval (extract v_3 32 64);
      let v_5 <- eval (concat (expression.bv_nat 32 0) v_4);
      let v_6 <- evaluateAddress mem_0;
      let v_7 <- load v_6 16;
      let (v_8 : expression (bv 32)) <- eval (extract v_7 32 64);
      let v_9 <- eval (concat (expression.bv_nat 32 0) v_8);
      let (v_10 : expression (bv 32)) <- eval (extract v_3 96 128);
      let v_11 <- eval (concat (expression.bv_nat 32 0) v_10);
      let (v_12 : expression (bv 32)) <- eval (extract v_7 96 128);
      let v_13 <- eval (concat (expression.bv_nat 32 0) v_12);
      let v_14 <- eval (concat (mul v_5 v_9) (mul v_11 v_13));
      setRegister (lhs.of_reg xmm_2) v_14;
      pure ()
     action;
    instr_pat $ fun (mem_0 : Mem) (ymm_1 : reg (bv 256)) (ymm_2 : reg (bv 256)) =>
     let action : semantics Unit := do
      let v_3 <- getRegister (lhs.of_reg ymm_1);
      let (v_4 : expression (bv 32)) <- eval (extract v_3 32 64);
      let v_5 <- eval (concat (expression.bv_nat 32 0) v_4);
      let v_6 <- evaluateAddress mem_0;
      let v_7 <- load v_6 32;
      let (v_8 : expression (bv 32)) <- eval (extract v_7 32 64);
      let v_9 <- eval (concat (expression.bv_nat 32 0) v_8);
      let (v_10 : expression (bv 32)) <- eval (extract v_3 96 128);
      let v_11 <- eval (concat (expression.bv_nat 32 0) v_10);
      let (v_12 : expression (bv 32)) <- eval (extract v_7 96 128);
      let v_13 <- eval (concat (expression.bv_nat 32 0) v_12);
      let (v_14 : expression (bv 32)) <- eval (extract v_3 160 192);
      let v_15 <- eval (concat (expression.bv_nat 32 0) v_14);
      let (v_16 : expression (bv 32)) <- eval (extract v_7 160 192);
      let v_17 <- eval (concat (expression.bv_nat 32 0) v_16);
      let (v_18 : expression (bv 32)) <- eval (extract v_3 224 256);
      let v_19 <- eval (concat (expression.bv_nat 32 0) v_18);
      let (v_20 : expression (bv 32)) <- eval (extract v_7 224 256);
      let v_21 <- eval (concat (expression.bv_nat 32 0) v_20);
      let v_22 <- eval (concat (mul v_15 v_17) (mul v_19 v_21));
      let v_23 <- eval (concat (mul v_11 v_13) v_22);
      let v_24 <- eval (concat (mul v_5 v_9) v_23);
      setRegister (lhs.of_reg ymm_2) v_24;
      pure ()
     action;
    instr_pat $ fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_3 <- getRegister (lhs.of_reg xmm_1);
      let (v_4 : expression (bv 32)) <- eval (extract v_3 32 64);
      let v_5 <- eval (concat (expression.bv_nat 32 0) v_4);
      let v_6 <- getRegister (lhs.of_reg xmm_0);
      let (v_7 : expression (bv 32)) <- eval (extract v_6 32 64);
      let v_8 <- eval (concat (expression.bv_nat 32 0) v_7);
      let (v_9 : expression (bv 32)) <- eval (extract v_3 96 128);
      let v_10 <- eval (concat (expression.bv_nat 32 0) v_9);
      let (v_11 : expression (bv 32)) <- eval (extract v_6 96 128);
      let v_12 <- eval (concat (expression.bv_nat 32 0) v_11);
      let v_13 <- eval (concat (mul v_5 v_8) (mul v_10 v_12));
      setRegister (lhs.of_reg xmm_2) v_13;
      pure ()
     action;
    instr_pat $ fun (ymm_0 : reg (bv 256)) (ymm_1 : reg (bv 256)) (ymm_2 : reg (bv 256)) =>
     let action : semantics Unit := do
      let v_3 <- getRegister (lhs.of_reg ymm_1);
      let (v_4 : expression (bv 32)) <- eval (extract v_3 32 64);
      let v_5 <- eval (concat (expression.bv_nat 32 0) v_4);
      let v_6 <- getRegister (lhs.of_reg ymm_0);
      let (v_7 : expression (bv 32)) <- eval (extract v_6 32 64);
      let v_8 <- eval (concat (expression.bv_nat 32 0) v_7);
      let (v_9 : expression (bv 32)) <- eval (extract v_3 96 128);
      let v_10 <- eval (concat (expression.bv_nat 32 0) v_9);
      let (v_11 : expression (bv 32)) <- eval (extract v_6 96 128);
      let v_12 <- eval (concat (expression.bv_nat 32 0) v_11);
      let (v_13 : expression (bv 32)) <- eval (extract v_3 160 192);
      let v_14 <- eval (concat (expression.bv_nat 32 0) v_13);
      let (v_15 : expression (bv 32)) <- eval (extract v_6 160 192);
      let v_16 <- eval (concat (expression.bv_nat 32 0) v_15);
      let (v_17 : expression (bv 32)) <- eval (extract v_3 224 256);
      let v_18 <- eval (concat (expression.bv_nat 32 0) v_17);
      let (v_19 : expression (bv 32)) <- eval (extract v_6 224 256);
      let v_20 <- eval (concat (expression.bv_nat 32 0) v_19);
      let v_21 <- eval (concat (mul v_14 v_16) (mul v_18 v_20));
      let v_22 <- eval (concat (mul v_10 v_12) v_21);
      let v_23 <- eval (concat (mul v_5 v_8) v_22);
      setRegister (lhs.of_reg ymm_2) v_23;
      pure ()
     action
