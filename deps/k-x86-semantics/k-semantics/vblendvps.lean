def vblendvps : instruction :=
  definst "vblendvps" $ do
    pattern fun (xmm_0 : reg (bv 128)) (mem_1 : Mem) (xmm_2 : reg (bv 128)) (xmm_3 : reg (bv 128)) => do
      v_4 <- getRegister (lhs.of_reg xmm_0);
      v_5 <- getRegister (lhs.of_reg xmm_2);
      (v_6 : expression (bv 32)) <- eval (extract v_5 0 32);
      v_7 <- evaluateAddress mem_1;
      v_8 <- load v_7 16;
      (v_9 : expression (bv 32)) <- eval (extract v_8 0 32);
      (v_10 : expression (bv 32)) <- eval (extract v_5 32 64);
      (v_11 : expression (bv 32)) <- eval (extract v_8 32 64);
      (v_12 : expression (bv 32)) <- eval (extract v_5 64 96);
      (v_13 : expression (bv 32)) <- eval (extract v_8 64 96);
      (v_14 : expression (bv 32)) <- eval (extract v_5 96 128);
      (v_15 : expression (bv 32)) <- eval (extract v_8 96 128);
      setRegister (lhs.of_reg xmm_3) (concat (mux (isBitClear v_4 0) v_6 v_9) (concat (mux (isBitClear v_4 32) v_10 v_11) (concat (mux (isBitClear v_4 64) v_12 v_13) (mux (isBitClear v_4 96) v_14 v_15))));
      pure ()
    pat_end;
    pattern fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) (xmm_3 : reg (bv 128)) => do
      v_4 <- getRegister (lhs.of_reg xmm_0);
      v_5 <- getRegister (lhs.of_reg xmm_2);
      (v_6 : expression (bv 32)) <- eval (extract v_5 0 32);
      v_7 <- getRegister (lhs.of_reg xmm_1);
      (v_8 : expression (bv 32)) <- eval (extract v_7 0 32);
      (v_9 : expression (bv 32)) <- eval (extract v_5 32 64);
      (v_10 : expression (bv 32)) <- eval (extract v_7 32 64);
      (v_11 : expression (bv 32)) <- eval (extract v_5 64 96);
      (v_12 : expression (bv 32)) <- eval (extract v_7 64 96);
      (v_13 : expression (bv 32)) <- eval (extract v_5 96 128);
      (v_14 : expression (bv 32)) <- eval (extract v_7 96 128);
      setRegister (lhs.of_reg xmm_3) (concat (mux (isBitClear v_4 0) v_6 v_8) (concat (mux (isBitClear v_4 32) v_9 v_10) (concat (mux (isBitClear v_4 64) v_11 v_12) (mux (isBitClear v_4 96) v_13 v_14))));
      pure ()
    pat_end;
    pattern fun (ymm_0 : reg (bv 256)) (mem_1 : Mem) (ymm_2 : reg (bv 256)) (ymm_3 : reg (bv 256)) => do
      v_4 <- getRegister (lhs.of_reg ymm_0);
      v_5 <- getRegister (lhs.of_reg ymm_2);
      (v_6 : expression (bv 32)) <- eval (extract v_5 0 32);
      v_7 <- evaluateAddress mem_1;
      v_8 <- load v_7 32;
      (v_9 : expression (bv 32)) <- eval (extract v_8 0 32);
      (v_10 : expression (bv 32)) <- eval (extract v_5 32 64);
      (v_11 : expression (bv 32)) <- eval (extract v_8 32 64);
      (v_12 : expression (bv 32)) <- eval (extract v_5 64 96);
      (v_13 : expression (bv 32)) <- eval (extract v_8 64 96);
      (v_14 : expression (bv 32)) <- eval (extract v_5 96 128);
      (v_15 : expression (bv 32)) <- eval (extract v_8 96 128);
      (v_16 : expression (bv 32)) <- eval (extract v_5 128 160);
      (v_17 : expression (bv 32)) <- eval (extract v_8 128 160);
      (v_18 : expression (bv 32)) <- eval (extract v_5 160 192);
      (v_19 : expression (bv 32)) <- eval (extract v_8 160 192);
      (v_20 : expression (bv 32)) <- eval (extract v_5 192 224);
      (v_21 : expression (bv 32)) <- eval (extract v_8 192 224);
      (v_22 : expression (bv 32)) <- eval (extract v_5 224 256);
      (v_23 : expression (bv 32)) <- eval (extract v_8 224 256);
      setRegister (lhs.of_reg ymm_3) (concat (mux (isBitClear v_4 0) v_6 v_9) (concat (mux (isBitClear v_4 32) v_10 v_11) (concat (mux (isBitClear v_4 64) v_12 v_13) (concat (mux (isBitClear v_4 96) v_14 v_15) (concat (mux (isBitClear v_4 128) v_16 v_17) (concat (mux (isBitClear v_4 160) v_18 v_19) (concat (mux (isBitClear v_4 192) v_20 v_21) (mux (isBitClear v_4 224) v_22 v_23))))))));
      pure ()
    pat_end;
    pattern fun (ymm_0 : reg (bv 256)) (ymm_1 : reg (bv 256)) (ymm_2 : reg (bv 256)) (ymm_3 : reg (bv 256)) => do
      v_4 <- getRegister (lhs.of_reg ymm_0);
      v_5 <- getRegister (lhs.of_reg ymm_2);
      (v_6 : expression (bv 32)) <- eval (extract v_5 0 32);
      v_7 <- getRegister (lhs.of_reg ymm_1);
      (v_8 : expression (bv 32)) <- eval (extract v_7 0 32);
      (v_9 : expression (bv 32)) <- eval (extract v_5 32 64);
      (v_10 : expression (bv 32)) <- eval (extract v_7 32 64);
      (v_11 : expression (bv 32)) <- eval (extract v_5 64 96);
      (v_12 : expression (bv 32)) <- eval (extract v_7 64 96);
      (v_13 : expression (bv 32)) <- eval (extract v_5 96 128);
      (v_14 : expression (bv 32)) <- eval (extract v_7 96 128);
      (v_15 : expression (bv 32)) <- eval (extract v_5 128 160);
      (v_16 : expression (bv 32)) <- eval (extract v_7 128 160);
      (v_17 : expression (bv 32)) <- eval (extract v_5 160 192);
      (v_18 : expression (bv 32)) <- eval (extract v_7 160 192);
      (v_19 : expression (bv 32)) <- eval (extract v_5 192 224);
      (v_20 : expression (bv 32)) <- eval (extract v_7 192 224);
      (v_21 : expression (bv 32)) <- eval (extract v_5 224 256);
      (v_22 : expression (bv 32)) <- eval (extract v_7 224 256);
      setRegister (lhs.of_reg ymm_3) (concat (mux (isBitClear v_4 0) v_6 v_8) (concat (mux (isBitClear v_4 32) v_9 v_10) (concat (mux (isBitClear v_4 64) v_11 v_12) (concat (mux (isBitClear v_4 96) v_13 v_14) (concat (mux (isBitClear v_4 128) v_15 v_16) (concat (mux (isBitClear v_4 160) v_17 v_18) (concat (mux (isBitClear v_4 192) v_19 v_20) (mux (isBitClear v_4 224) v_21 v_22))))))));
      pure ()
    pat_end
