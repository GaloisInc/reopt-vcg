def vpmaskmovd : instruction :=
  definst "vpmaskmovd" $ do
    pattern fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) => do
      v_3 <- getRegister (lhs.of_reg xmm_1);
      v_4 <- evaluateAddress mem_0;
      v_5 <- load v_4 16;
      setRegister (lhs.of_reg xmm_2) (concat (mux (isBitSet v_3 0) (extract v_5 0 32) (expression.bv_nat 32 0)) (concat (mux (isBitSet v_3 32) (extract v_5 32 64) (expression.bv_nat 32 0)) (concat (mux (isBitSet v_3 64) (extract v_5 64 96) (expression.bv_nat 32 0)) (mux (isBitSet v_3 96) (extract v_5 96 128) (expression.bv_nat 32 0)))));
      pure ()
    pat_end;
    pattern fun (mem_0 : Mem) (ymm_1 : reg (bv 256)) (ymm_2 : reg (bv 256)) => do
      v_3 <- getRegister (lhs.of_reg ymm_1);
      v_4 <- evaluateAddress mem_0;
      v_5 <- load v_4 32;
      setRegister (lhs.of_reg ymm_2) (concat (mux (isBitSet v_3 0) (extract v_5 0 32) (expression.bv_nat 32 0)) (concat (mux (isBitSet v_3 32) (extract v_5 32 64) (expression.bv_nat 32 0)) (concat (mux (isBitSet v_3 64) (extract v_5 64 96) (expression.bv_nat 32 0)) (concat (mux (isBitSet v_3 96) (extract v_5 96 128) (expression.bv_nat 32 0)) (concat (mux (isBitSet v_3 128) (extract v_5 128 160) (expression.bv_nat 32 0)) (concat (mux (isBitSet v_3 160) (extract v_5 160 192) (expression.bv_nat 32 0)) (concat (mux (isBitSet v_3 192) (extract v_5 192 224) (expression.bv_nat 32 0)) (mux (isBitSet v_3 224) (extract v_5 224 256) (expression.bv_nat 32 0)))))))));
      pure ()
    pat_end;
    pattern fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) (mem_2 : Mem) => do
      v_3 <- evaluateAddress mem_2;
      v_4 <- getRegister (lhs.of_reg xmm_1);
      v_5 <- getRegister (lhs.of_reg xmm_0);
      v_6 <- load v_3 16;
      store v_3 (concat (mux (isBitSet v_4 0) (extract v_5 0 32) (extract v_6 0 32)) (concat (mux (isBitSet v_4 32) (extract v_5 32 64) (extract v_6 32 64)) (concat (mux (isBitSet v_4 64) (extract v_5 64 96) (extract v_6 64 96)) (mux (isBitSet v_4 96) (extract v_5 96 128) (extract v_6 96 128))))) 16;
      pure ()
    pat_end;
    pattern fun (ymm_0 : reg (bv 256)) (ymm_1 : reg (bv 256)) (mem_2 : Mem) => do
      v_3 <- evaluateAddress mem_2;
      v_4 <- getRegister (lhs.of_reg ymm_1);
      v_5 <- getRegister (lhs.of_reg ymm_0);
      v_6 <- load v_3 32;
      store v_3 (concat (mux (isBitSet v_4 0) (extract v_5 0 32) (extract v_6 0 32)) (concat (mux (isBitSet v_4 32) (extract v_5 32 64) (extract v_6 32 64)) (concat (mux (isBitSet v_4 64) (extract v_5 64 96) (extract v_6 64 96)) (concat (mux (isBitSet v_4 96) (extract v_5 96 128) (extract v_6 96 128)) (concat (mux (isBitSet v_4 128) (extract v_5 128 160) (extract v_6 128 160)) (concat (mux (isBitSet v_4 160) (extract v_5 160 192) (extract v_6 160 192)) (concat (mux (isBitSet v_4 192) (extract v_5 192 224) (extract v_6 192 224)) (mux (isBitSet v_4 224) (extract v_5 224 256) (extract v_6 224 256))))))))) 32;
      pure ()
    pat_end
