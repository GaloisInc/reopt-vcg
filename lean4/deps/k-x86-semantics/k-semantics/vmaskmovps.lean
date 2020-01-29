def vmaskmovps : instruction :=
  definst "vmaskmovps" $ do
    pattern fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) => do
      v_3 <- getRegister (lhs.of_reg xmm_1);
      v_4 <- evaluateAddress mem_0;
      v_5 <- load v_4 16;
      (v_6 : expression (bv 32)) <- eval (extract v_5 0 32);
      (v_7 : expression (bv 32)) <- eval (extract v_5 32 64);
      (v_8 : expression (bv 32)) <- eval (extract v_5 64 96);
      (v_9 : expression (bv 32)) <- eval (extract v_5 96 128);
      setRegister (lhs.of_reg xmm_2) (concat (mux (isBitSet v_3 0) v_6 (expression.bv_nat 32 0)) (concat (mux (isBitSet v_3 32) v_7 (expression.bv_nat 32 0)) (concat (mux (isBitSet v_3 64) v_8 (expression.bv_nat 32 0)) (mux (isBitSet v_3 96) v_9 (expression.bv_nat 32 0)))));
      pure ()
    pat_end;
    pattern fun (mem_0 : Mem) (ymm_1 : reg (bv 256)) (ymm_2 : reg (bv 256)) => do
      v_3 <- getRegister (lhs.of_reg ymm_1);
      v_4 <- evaluateAddress mem_0;
      v_5 <- load v_4 32;
      (v_6 : expression (bv 32)) <- eval (extract v_5 0 32);
      (v_7 : expression (bv 32)) <- eval (extract v_5 32 64);
      (v_8 : expression (bv 32)) <- eval (extract v_5 64 96);
      (v_9 : expression (bv 32)) <- eval (extract v_5 96 128);
      (v_10 : expression (bv 32)) <- eval (extract v_5 128 160);
      (v_11 : expression (bv 32)) <- eval (extract v_5 160 192);
      (v_12 : expression (bv 32)) <- eval (extract v_5 192 224);
      (v_13 : expression (bv 32)) <- eval (extract v_5 224 256);
      setRegister (lhs.of_reg ymm_2) (concat (mux (isBitSet v_3 0) v_6 (expression.bv_nat 32 0)) (concat (mux (isBitSet v_3 32) v_7 (expression.bv_nat 32 0)) (concat (mux (isBitSet v_3 64) v_8 (expression.bv_nat 32 0)) (concat (mux (isBitSet v_3 96) v_9 (expression.bv_nat 32 0)) (concat (mux (isBitSet v_3 128) v_10 (expression.bv_nat 32 0)) (concat (mux (isBitSet v_3 160) v_11 (expression.bv_nat 32 0)) (concat (mux (isBitSet v_3 192) v_12 (expression.bv_nat 32 0)) (mux (isBitSet v_3 224) v_13 (expression.bv_nat 32 0)))))))));
      pure ()
    pat_end;
    pattern fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) (mem_2 : Mem) => do
      v_3 <- evaluateAddress mem_2;
      v_4 <- getRegister (lhs.of_reg xmm_1);
      v_5 <- getRegister (lhs.of_reg xmm_0);
      (v_6 : expression (bv 32)) <- eval (extract v_5 0 32);
      v_7 <- load v_3 16;
      (v_8 : expression (bv 32)) <- eval (extract v_7 0 32);
      (v_9 : expression (bv 32)) <- eval (extract v_5 32 64);
      (v_10 : expression (bv 32)) <- eval (extract v_7 32 64);
      (v_11 : expression (bv 32)) <- eval (extract v_5 64 96);
      (v_12 : expression (bv 32)) <- eval (extract v_7 64 96);
      (v_13 : expression (bv 32)) <- eval (extract v_5 96 128);
      (v_14 : expression (bv 32)) <- eval (extract v_7 96 128);
      store v_3 (concat (mux (isBitSet v_4 0) v_6 v_8) (concat (mux (isBitSet v_4 32) v_9 v_10) (concat (mux (isBitSet v_4 64) v_11 v_12) (mux (isBitSet v_4 96) v_13 v_14)))) 16;
      pure ()
    pat_end;
    pattern fun (ymm_0 : reg (bv 256)) (ymm_1 : reg (bv 256)) (mem_2 : Mem) => do
      v_3 <- evaluateAddress mem_2;
      v_4 <- getRegister (lhs.of_reg ymm_1);
      v_5 <- getRegister (lhs.of_reg ymm_0);
      (v_6 : expression (bv 32)) <- eval (extract v_5 0 32);
      v_7 <- load v_3 32;
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
      store v_3 (concat (mux (isBitSet v_4 0) v_6 v_8) (concat (mux (isBitSet v_4 32) v_9 v_10) (concat (mux (isBitSet v_4 64) v_11 v_12) (concat (mux (isBitSet v_4 96) v_13 v_14) (concat (mux (isBitSet v_4 128) v_15 v_16) (concat (mux (isBitSet v_4 160) v_17 v_18) (concat (mux (isBitSet v_4 192) v_19 v_20) (mux (isBitSet v_4 224) v_21 v_22)))))))) 32;
      pure ()
    pat_end
