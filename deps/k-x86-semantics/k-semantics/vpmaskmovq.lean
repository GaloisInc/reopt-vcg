def vpmaskmovq : instruction :=
  definst "vpmaskmovq" $ do
    instr_pat $ fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_3 <- getRegister (lhs.of_reg xmm_1);
      let v_4 <- evaluateAddress mem_0;
      let v_5 <- load v_4 16;
      let (v_6 : expression (bv 64)) <- eval (extract v_5 0 64);
      let (v_7 : expression (bv 64)) <- eval (extract v_5 64 128);
      let v_8 <- eval (concat (mux (isBitSet v_3 0) v_6 (expression.bv_nat 64 0)) (mux (isBitSet v_3 64) v_7 (expression.bv_nat 64 0)));
      setRegister (lhs.of_reg xmm_2) v_8;
      pure ()
     action;
    instr_pat $ fun (mem_0 : Mem) (ymm_1 : reg (bv 256)) (ymm_2 : reg (bv 256)) =>
     let action : semantics Unit := do
      let v_3 <- getRegister (lhs.of_reg ymm_1);
      let v_4 <- evaluateAddress mem_0;
      let v_5 <- load v_4 32;
      let (v_6 : expression (bv 64)) <- eval (extract v_5 0 64);
      let (v_7 : expression (bv 64)) <- eval (extract v_5 64 128);
      let (v_8 : expression (bv 64)) <- eval (extract v_5 128 192);
      let (v_9 : expression (bv 64)) <- eval (extract v_5 192 256);
      let v_10 <- eval (concat (mux (isBitSet v_3 128) v_8 (expression.bv_nat 64 0)) (mux (isBitSet v_3 192) v_9 (expression.bv_nat 64 0)));
      let v_11 <- eval (concat (mux (isBitSet v_3 64) v_7 (expression.bv_nat 64 0)) v_10);
      let v_12 <- eval (concat (mux (isBitSet v_3 0) v_6 (expression.bv_nat 64 0)) v_11);
      setRegister (lhs.of_reg ymm_2) v_12;
      pure ()
     action;
    instr_pat $ fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) (mem_2 : Mem) =>
     let action : semantics Unit := do
      let v_3 <- evaluateAddress mem_2;
      let v_4 <- getRegister (lhs.of_reg xmm_1);
      let v_5 <- getRegister (lhs.of_reg xmm_0);
      let (v_6 : expression (bv 64)) <- eval (extract v_5 0 64);
      let v_7 <- load v_3 16;
      let (v_8 : expression (bv 64)) <- eval (extract v_7 0 64);
      let (v_9 : expression (bv 64)) <- eval (extract v_5 64 128);
      let (v_10 : expression (bv 64)) <- eval (extract v_7 64 128);
      let v_11 <- eval (concat (mux (isBitSet v_4 0) v_6 v_8) (mux (isBitSet v_4 64) v_9 v_10));
      store v_3 v_11 16;
      pure ()
     action;
    instr_pat $ fun (ymm_0 : reg (bv 256)) (ymm_1 : reg (bv 256)) (mem_2 : Mem) =>
     let action : semantics Unit := do
      let v_3 <- evaluateAddress mem_2;
      let v_4 <- getRegister (lhs.of_reg ymm_1);
      let v_5 <- getRegister (lhs.of_reg ymm_0);
      let (v_6 : expression (bv 64)) <- eval (extract v_5 0 64);
      let v_7 <- load v_3 32;
      let (v_8 : expression (bv 64)) <- eval (extract v_7 0 64);
      let (v_9 : expression (bv 64)) <- eval (extract v_5 64 128);
      let (v_10 : expression (bv 64)) <- eval (extract v_7 64 128);
      let (v_11 : expression (bv 64)) <- eval (extract v_5 128 192);
      let (v_12 : expression (bv 64)) <- eval (extract v_7 128 192);
      let (v_13 : expression (bv 64)) <- eval (extract v_5 192 256);
      let (v_14 : expression (bv 64)) <- eval (extract v_7 192 256);
      let v_15 <- eval (concat (mux (isBitSet v_4 128) v_11 v_12) (mux (isBitSet v_4 192) v_13 v_14));
      let v_16 <- eval (concat (mux (isBitSet v_4 64) v_9 v_10) v_15);
      let v_17 <- eval (concat (mux (isBitSet v_4 0) v_6 v_8) v_16);
      store v_3 v_17 32;
      pure ()
     action
