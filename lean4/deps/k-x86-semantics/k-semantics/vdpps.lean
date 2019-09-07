def vdpps1 : instruction :=
  definst "vdpps" $ do
    pattern fun (imm_0 : imm int) (mem_1 : Mem) (xmm_2 : reg (bv 128)) (xmm_3 : reg (bv 128)) => do
      v_4 <- eval (handleImmediateWithSignExtend imm_0 8 8);
      v_5 <- getRegister xmm_2;
      v_6 <- evaluateAddress mem_1;
      v_7 <- load v_6 16;
      v_8 <- eval (Float2MInt (_+Float__FLOAT (MInt2Float (Float2MInt (_+Float__FLOAT (MInt2Float (mux (isBitSet v_4 3) (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_5 96 128) 24 8) (MInt2Float (extract v_7 96 128) 24 8)) 32) (expression.bv_nat 32 0)) 24 8) (MInt2Float (mux (isBitSet v_4 2) (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_5 64 96) 24 8) (MInt2Float (extract v_7 64 96) 24 8)) 32) (expression.bv_nat 32 0)) 24 8)) 32) 24 8) (MInt2Float (Float2MInt (_+Float__FLOAT (MInt2Float (mux (isBitSet v_4 1) (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_5 32 64) 24 8) (MInt2Float (extract v_7 32 64) 24 8)) 32) (expression.bv_nat 32 0)) 24 8) (MInt2Float (mux (isBitSet v_4 0) (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_5 0 32) 24 8) (MInt2Float (extract v_7 0 32) 24 8)) 32) (expression.bv_nat 32 0)) 24 8)) 32) 24 8)) 32);
      setRegister (lhs.of_reg xmm_3) (concat (concat (concat (mux (isBitSet v_4 4) v_8 (expression.bv_nat 32 0)) (mux (isBitSet v_4 5) v_8 (expression.bv_nat 32 0))) (mux (isBitSet v_4 6) v_8 (expression.bv_nat 32 0))) (mux (isBitSet v_4 7) v_8 (expression.bv_nat 32 0)));
      pure ()
    pat_end;
    pattern fun (imm_0 : imm int) (mem_1 : Mem) (ymm_2 : reg (bv 256)) (ymm_3 : reg (bv 256)) => do
      v_4 <- eval (handleImmediateWithSignExtend imm_0 8 8);
      v_5 <- eval (isBitSet v_4 4);
      v_6 <- eval (isBitSet v_4 3);
      v_7 <- getRegister ymm_2;
      v_8 <- evaluateAddress mem_1;
      v_9 <- load v_8 32;
      v_10 <- eval (isBitSet v_4 2);
      v_11 <- eval (isBitSet v_4 1);
      v_12 <- eval (isBitSet v_4 0);
      v_13 <- eval (Float2MInt (_+Float__FLOAT (MInt2Float (Float2MInt (_+Float__FLOAT (MInt2Float (mux v_6 (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_7 96 128) 24 8) (MInt2Float (extract v_9 96 128) 24 8)) 32) (expression.bv_nat 32 0)) 24 8) (MInt2Float (mux v_10 (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_7 64 96) 24 8) (MInt2Float (extract v_9 64 96) 24 8)) 32) (expression.bv_nat 32 0)) 24 8)) 32) 24 8) (MInt2Float (Float2MInt (_+Float__FLOAT (MInt2Float (mux v_11 (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_7 32 64) 24 8) (MInt2Float (extract v_9 32 64) 24 8)) 32) (expression.bv_nat 32 0)) 24 8) (MInt2Float (mux v_12 (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_7 0 32) 24 8) (MInt2Float (extract v_9 0 32) 24 8)) 32) (expression.bv_nat 32 0)) 24 8)) 32) 24 8)) 32);
      v_14 <- eval (isBitSet v_4 5);
      v_15 <- eval (isBitSet v_4 6);
      v_16 <- eval (isBitSet v_4 7);
      v_17 <- eval (Float2MInt (_+Float__FLOAT (MInt2Float (Float2MInt (_+Float__FLOAT (MInt2Float (mux v_6 (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_7 224 256) 24 8) (MInt2Float (extract v_9 224 256) 24 8)) 32) (expression.bv_nat 32 0)) 24 8) (MInt2Float (mux v_10 (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_7 192 224) 24 8) (MInt2Float (extract v_9 192 224) 24 8)) 32) (expression.bv_nat 32 0)) 24 8)) 32) 24 8) (MInt2Float (Float2MInt (_+Float__FLOAT (MInt2Float (mux v_11 (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_7 160 192) 24 8) (MInt2Float (extract v_9 160 192) 24 8)) 32) (expression.bv_nat 32 0)) 24 8) (MInt2Float (mux v_12 (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_7 128 160) 24 8) (MInt2Float (extract v_9 128 160) 24 8)) 32) (expression.bv_nat 32 0)) 24 8)) 32) 24 8)) 32);
      setRegister (lhs.of_reg ymm_3) (concat (concat (concat (concat (mux v_5 v_13 (expression.bv_nat 32 0)) (mux v_14 v_13 (expression.bv_nat 32 0))) (mux v_15 v_13 (expression.bv_nat 32 0))) (mux v_16 v_13 (expression.bv_nat 32 0))) (concat (concat (concat (mux v_5 v_17 (expression.bv_nat 32 0)) (mux v_14 v_17 (expression.bv_nat 32 0))) (mux v_15 v_17 (expression.bv_nat 32 0))) (mux v_16 v_17 (expression.bv_nat 32 0))));
      pure ()
    pat_end;
    pattern fun (imm_0 : imm int) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) (xmm_3 : reg (bv 128)) => do
      v_4 <- eval (handleImmediateWithSignExtend imm_0 8 8);
      v_5 <- getRegister xmm_2;
      v_6 <- getRegister xmm_1;
      v_7 <- eval (Float2MInt (_+Float__FLOAT (MInt2Float (Float2MInt (_+Float__FLOAT (MInt2Float (mux (isBitSet v_4 3) (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_5 96 128) 24 8) (MInt2Float (extract v_6 96 128) 24 8)) 32) (expression.bv_nat 32 0)) 24 8) (MInt2Float (mux (isBitSet v_4 2) (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_5 64 96) 24 8) (MInt2Float (extract v_6 64 96) 24 8)) 32) (expression.bv_nat 32 0)) 24 8)) 32) 24 8) (MInt2Float (Float2MInt (_+Float__FLOAT (MInt2Float (mux (isBitSet v_4 1) (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_5 32 64) 24 8) (MInt2Float (extract v_6 32 64) 24 8)) 32) (expression.bv_nat 32 0)) 24 8) (MInt2Float (mux (isBitSet v_4 0) (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_5 0 32) 24 8) (MInt2Float (extract v_6 0 32) 24 8)) 32) (expression.bv_nat 32 0)) 24 8)) 32) 24 8)) 32);
      setRegister (lhs.of_reg xmm_3) (concat (concat (concat (mux (isBitSet v_4 4) v_7 (expression.bv_nat 32 0)) (mux (isBitSet v_4 5) v_7 (expression.bv_nat 32 0))) (mux (isBitSet v_4 6) v_7 (expression.bv_nat 32 0))) (mux (isBitSet v_4 7) v_7 (expression.bv_nat 32 0)));
      pure ()
    pat_end;
    pattern fun (imm_0 : imm int) (ymm_1 : reg (bv 256)) (ymm_2 : reg (bv 256)) (ymm_3 : reg (bv 256)) => do
      v_4 <- eval (handleImmediateWithSignExtend imm_0 8 8);
      v_5 <- eval (isBitSet v_4 4);
      v_6 <- eval (isBitSet v_4 3);
      v_7 <- getRegister ymm_2;
      v_8 <- getRegister ymm_1;
      v_9 <- eval (isBitSet v_4 2);
      v_10 <- eval (isBitSet v_4 1);
      v_11 <- eval (isBitSet v_4 0);
      v_12 <- eval (Float2MInt (_+Float__FLOAT (MInt2Float (Float2MInt (_+Float__FLOAT (MInt2Float (mux v_6 (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_7 96 128) 24 8) (MInt2Float (extract v_8 96 128) 24 8)) 32) (expression.bv_nat 32 0)) 24 8) (MInt2Float (mux v_9 (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_7 64 96) 24 8) (MInt2Float (extract v_8 64 96) 24 8)) 32) (expression.bv_nat 32 0)) 24 8)) 32) 24 8) (MInt2Float (Float2MInt (_+Float__FLOAT (MInt2Float (mux v_10 (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_7 32 64) 24 8) (MInt2Float (extract v_8 32 64) 24 8)) 32) (expression.bv_nat 32 0)) 24 8) (MInt2Float (mux v_11 (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_7 0 32) 24 8) (MInt2Float (extract v_8 0 32) 24 8)) 32) (expression.bv_nat 32 0)) 24 8)) 32) 24 8)) 32);
      v_13 <- eval (isBitSet v_4 5);
      v_14 <- eval (isBitSet v_4 6);
      v_15 <- eval (isBitSet v_4 7);
      v_16 <- eval (Float2MInt (_+Float__FLOAT (MInt2Float (Float2MInt (_+Float__FLOAT (MInt2Float (mux v_6 (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_7 224 256) 24 8) (MInt2Float (extract v_8 224 256) 24 8)) 32) (expression.bv_nat 32 0)) 24 8) (MInt2Float (mux v_9 (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_7 192 224) 24 8) (MInt2Float (extract v_8 192 224) 24 8)) 32) (expression.bv_nat 32 0)) 24 8)) 32) 24 8) (MInt2Float (Float2MInt (_+Float__FLOAT (MInt2Float (mux v_10 (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_7 160 192) 24 8) (MInt2Float (extract v_8 160 192) 24 8)) 32) (expression.bv_nat 32 0)) 24 8) (MInt2Float (mux v_11 (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_7 128 160) 24 8) (MInt2Float (extract v_8 128 160) 24 8)) 32) (expression.bv_nat 32 0)) 24 8)) 32) 24 8)) 32);
      setRegister (lhs.of_reg ymm_3) (concat (concat (concat (concat (mux v_5 v_12 (expression.bv_nat 32 0)) (mux v_13 v_12 (expression.bv_nat 32 0))) (mux v_14 v_12 (expression.bv_nat 32 0))) (mux v_15 v_12 (expression.bv_nat 32 0))) (concat (concat (concat (mux v_5 v_16 (expression.bv_nat 32 0)) (mux v_13 v_16 (expression.bv_nat 32 0))) (mux v_14 v_16 (expression.bv_nat 32 0))) (mux v_15 v_16 (expression.bv_nat 32 0))));
      pure ()
    pat_end
