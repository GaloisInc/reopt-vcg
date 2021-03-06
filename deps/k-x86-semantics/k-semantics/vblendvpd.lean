def vblendvpd : instruction :=
  definst "vblendvpd" $ do
    instr_pat $ fun (xmm_0 : reg (bv 128)) (mem_1 : Mem) (xmm_2 : reg (bv 128)) (xmm_3 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_4 <- getRegister (lhs.of_reg xmm_0);
      let v_5 <- getRegister (lhs.of_reg xmm_2);
      let (v_6 : expression (bv 64)) <- eval (extract v_5 0 64);
      let v_7 <- evaluateAddress mem_1;
      let v_8 <- load v_7 16;
      let (v_9 : expression (bv 64)) <- eval (extract v_8 0 64);
      let (v_10 : expression (bv 64)) <- eval (extract v_5 64 128);
      let (v_11 : expression (bv 64)) <- eval (extract v_8 64 128);
      let v_12 <- eval (concat (mux (isBitClear v_4 0) v_6 v_9) (mux (isBitClear v_4 64) v_10 v_11));
      setRegister (lhs.of_reg xmm_3) v_12;
      pure ()
     action;
    instr_pat $ fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) (xmm_3 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_4 <- getRegister (lhs.of_reg xmm_0);
      let v_5 <- getRegister (lhs.of_reg xmm_2);
      let (v_6 : expression (bv 64)) <- eval (extract v_5 0 64);
      let v_7 <- getRegister (lhs.of_reg xmm_1);
      let (v_8 : expression (bv 64)) <- eval (extract v_7 0 64);
      let (v_9 : expression (bv 64)) <- eval (extract v_5 64 128);
      let (v_10 : expression (bv 64)) <- eval (extract v_7 64 128);
      let v_11 <- eval (concat (mux (isBitClear v_4 0) v_6 v_8) (mux (isBitClear v_4 64) v_9 v_10));
      setRegister (lhs.of_reg xmm_3) v_11;
      pure ()
     action;
    instr_pat $ fun (ymm_0 : reg (bv 256)) (mem_1 : Mem) (ymm_2 : reg (bv 256)) (ymm_3 : reg (bv 256)) =>
     let action : semantics Unit := do
      let v_4 <- getRegister (lhs.of_reg ymm_0);
      let v_5 <- getRegister (lhs.of_reg ymm_2);
      let (v_6 : expression (bv 64)) <- eval (extract v_5 0 64);
      let v_7 <- evaluateAddress mem_1;
      let v_8 <- load v_7 32;
      let (v_9 : expression (bv 64)) <- eval (extract v_8 0 64);
      let (v_10 : expression (bv 64)) <- eval (extract v_5 64 128);
      let (v_11 : expression (bv 64)) <- eval (extract v_8 64 128);
      let (v_12 : expression (bv 64)) <- eval (extract v_5 128 192);
      let (v_13 : expression (bv 64)) <- eval (extract v_8 128 192);
      let (v_14 : expression (bv 64)) <- eval (extract v_5 192 256);
      let (v_15 : expression (bv 64)) <- eval (extract v_8 192 256);
      let v_16 <- eval (concat (mux (isBitClear v_4 128) v_12 v_13) (mux (isBitClear v_4 192) v_14 v_15));
      let v_17 <- eval (concat (mux (isBitClear v_4 64) v_10 v_11) v_16);
      let v_18 <- eval (concat (mux (isBitClear v_4 0) v_6 v_9) v_17);
      setRegister (lhs.of_reg ymm_3) v_18;
      pure ()
     action;
    instr_pat $ fun (ymm_0 : reg (bv 256)) (ymm_1 : reg (bv 256)) (ymm_2 : reg (bv 256)) (ymm_3 : reg (bv 256)) =>
     let action : semantics Unit := do
      let v_4 <- getRegister (lhs.of_reg ymm_0);
      let v_5 <- getRegister (lhs.of_reg ymm_2);
      let (v_6 : expression (bv 64)) <- eval (extract v_5 0 64);
      let v_7 <- getRegister (lhs.of_reg ymm_1);
      let (v_8 : expression (bv 64)) <- eval (extract v_7 0 64);
      let (v_9 : expression (bv 64)) <- eval (extract v_5 64 128);
      let (v_10 : expression (bv 64)) <- eval (extract v_7 64 128);
      let (v_11 : expression (bv 64)) <- eval (extract v_5 128 192);
      let (v_12 : expression (bv 64)) <- eval (extract v_7 128 192);
      let (v_13 : expression (bv 64)) <- eval (extract v_5 192 256);
      let (v_14 : expression (bv 64)) <- eval (extract v_7 192 256);
      let v_15 <- eval (concat (mux (isBitClear v_4 128) v_11 v_12) (mux (isBitClear v_4 192) v_13 v_14));
      let v_16 <- eval (concat (mux (isBitClear v_4 64) v_9 v_10) v_15);
      let v_17 <- eval (concat (mux (isBitClear v_4 0) v_6 v_8) v_16);
      setRegister (lhs.of_reg ymm_3) v_17;
      pure ()
     action
