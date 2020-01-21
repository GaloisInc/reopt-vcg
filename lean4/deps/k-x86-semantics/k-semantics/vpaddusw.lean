def vpaddusw : instruction :=
  definst "vpaddusw" $ do
    pattern fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) => do
      v_3 <- getRegister (lhs.of_reg xmm_1);
      v_4 <- evaluateAddress mem_0;
      v_5 <- load v_4 16;
      v_6 <- eval (add (concat (expression.bv_nat 1 0) (extract v_3 0 16)) (concat (expression.bv_nat 1 0) (extract v_5 0 16)));
      v_7 <- eval (add (concat (expression.bv_nat 1 0) (extract v_3 16 32)) (concat (expression.bv_nat 1 0) (extract v_5 16 32)));
      v_8 <- eval (add (concat (expression.bv_nat 1 0) (extract v_3 32 48)) (concat (expression.bv_nat 1 0) (extract v_5 32 48)));
      v_9 <- eval (add (concat (expression.bv_nat 1 0) (extract v_3 48 64)) (concat (expression.bv_nat 1 0) (extract v_5 48 64)));
      v_10 <- eval (add (concat (expression.bv_nat 1 0) (extract v_3 64 80)) (concat (expression.bv_nat 1 0) (extract v_5 64 80)));
      v_11 <- eval (add (concat (expression.bv_nat 1 0) (extract v_3 80 96)) (concat (expression.bv_nat 1 0) (extract v_5 80 96)));
      v_12 <- eval (add (concat (expression.bv_nat 1 0) (extract v_3 96 112)) (concat (expression.bv_nat 1 0) (extract v_5 96 112)));
      v_13 <- eval (add (concat (expression.bv_nat 1 0) (extract v_3 112 128)) (concat (expression.bv_nat 1 0) (extract v_5 112 128)));
      setRegister (lhs.of_reg xmm_2) (concat (mux (isBitSet v_6 0) (expression.bv_nat 16 65535) (extract v_6 1 17)) (concat (mux (isBitSet v_7 0) (expression.bv_nat 16 65535) (extract v_7 1 17)) (concat (mux (isBitSet v_8 0) (expression.bv_nat 16 65535) (extract v_8 1 17)) (concat (mux (isBitSet v_9 0) (expression.bv_nat 16 65535) (extract v_9 1 17)) (concat (mux (isBitSet v_10 0) (expression.bv_nat 16 65535) (extract v_10 1 17)) (concat (mux (isBitSet v_11 0) (expression.bv_nat 16 65535) (extract v_11 1 17)) (concat (mux (isBitSet v_12 0) (expression.bv_nat 16 65535) (extract v_12 1 17)) (mux (isBitSet v_13 0) (expression.bv_nat 16 65535) (extract v_13 1 17)))))))));
      pure ()
    pat_end;
    pattern fun (mem_0 : Mem) (ymm_1 : reg (bv 256)) (ymm_2 : reg (bv 256)) => do
      v_3 <- getRegister (lhs.of_reg ymm_1);
      v_4 <- evaluateAddress mem_0;
      v_5 <- load v_4 32;
      v_6 <- eval (add (concat (expression.bv_nat 1 0) (extract v_3 0 16)) (concat (expression.bv_nat 1 0) (extract v_5 0 16)));
      v_7 <- eval (add (concat (expression.bv_nat 1 0) (extract v_3 16 32)) (concat (expression.bv_nat 1 0) (extract v_5 16 32)));
      v_8 <- eval (add (concat (expression.bv_nat 1 0) (extract v_3 32 48)) (concat (expression.bv_nat 1 0) (extract v_5 32 48)));
      v_9 <- eval (add (concat (expression.bv_nat 1 0) (extract v_3 48 64)) (concat (expression.bv_nat 1 0) (extract v_5 48 64)));
      v_10 <- eval (add (concat (expression.bv_nat 1 0) (extract v_3 64 80)) (concat (expression.bv_nat 1 0) (extract v_5 64 80)));
      v_11 <- eval (add (concat (expression.bv_nat 1 0) (extract v_3 80 96)) (concat (expression.bv_nat 1 0) (extract v_5 80 96)));
      v_12 <- eval (add (concat (expression.bv_nat 1 0) (extract v_3 96 112)) (concat (expression.bv_nat 1 0) (extract v_5 96 112)));
      v_13 <- eval (add (concat (expression.bv_nat 1 0) (extract v_3 112 128)) (concat (expression.bv_nat 1 0) (extract v_5 112 128)));
      v_14 <- eval (add (concat (expression.bv_nat 1 0) (extract v_3 128 144)) (concat (expression.bv_nat 1 0) (extract v_5 128 144)));
      v_15 <- eval (add (concat (expression.bv_nat 1 0) (extract v_3 144 160)) (concat (expression.bv_nat 1 0) (extract v_5 144 160)));
      v_16 <- eval (add (concat (expression.bv_nat 1 0) (extract v_3 160 176)) (concat (expression.bv_nat 1 0) (extract v_5 160 176)));
      v_17 <- eval (add (concat (expression.bv_nat 1 0) (extract v_3 176 192)) (concat (expression.bv_nat 1 0) (extract v_5 176 192)));
      v_18 <- eval (add (concat (expression.bv_nat 1 0) (extract v_3 192 208)) (concat (expression.bv_nat 1 0) (extract v_5 192 208)));
      v_19 <- eval (add (concat (expression.bv_nat 1 0) (extract v_3 208 224)) (concat (expression.bv_nat 1 0) (extract v_5 208 224)));
      v_20 <- eval (add (concat (expression.bv_nat 1 0) (extract v_3 224 240)) (concat (expression.bv_nat 1 0) (extract v_5 224 240)));
      v_21 <- eval (add (concat (expression.bv_nat 1 0) (extract v_3 240 256)) (concat (expression.bv_nat 1 0) (extract v_5 240 256)));
      setRegister (lhs.of_reg ymm_2) (concat (mux (isBitSet v_6 0) (expression.bv_nat 16 65535) (extract v_6 1 17)) (concat (mux (isBitSet v_7 0) (expression.bv_nat 16 65535) (extract v_7 1 17)) (concat (mux (isBitSet v_8 0) (expression.bv_nat 16 65535) (extract v_8 1 17)) (concat (mux (isBitSet v_9 0) (expression.bv_nat 16 65535) (extract v_9 1 17)) (concat (mux (isBitSet v_10 0) (expression.bv_nat 16 65535) (extract v_10 1 17)) (concat (mux (isBitSet v_11 0) (expression.bv_nat 16 65535) (extract v_11 1 17)) (concat (mux (isBitSet v_12 0) (expression.bv_nat 16 65535) (extract v_12 1 17)) (concat (mux (isBitSet v_13 0) (expression.bv_nat 16 65535) (extract v_13 1 17)) (concat (mux (isBitSet v_14 0) (expression.bv_nat 16 65535) (extract v_14 1 17)) (concat (mux (isBitSet v_15 0) (expression.bv_nat 16 65535) (extract v_15 1 17)) (concat (mux (isBitSet v_16 0) (expression.bv_nat 16 65535) (extract v_16 1 17)) (concat (mux (isBitSet v_17 0) (expression.bv_nat 16 65535) (extract v_17 1 17)) (concat (mux (isBitSet v_18 0) (expression.bv_nat 16 65535) (extract v_18 1 17)) (concat (mux (isBitSet v_19 0) (expression.bv_nat 16 65535) (extract v_19 1 17)) (concat (mux (isBitSet v_20 0) (expression.bv_nat 16 65535) (extract v_20 1 17)) (mux (isBitSet v_21 0) (expression.bv_nat 16 65535) (extract v_21 1 17)))))))))))))))));
      pure ()
    pat_end;
    pattern fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) => do
      v_3 <- getRegister (lhs.of_reg xmm_1);
      v_4 <- getRegister (lhs.of_reg xmm_0);
      v_5 <- eval (add (concat (expression.bv_nat 1 0) (extract v_3 0 16)) (concat (expression.bv_nat 1 0) (extract v_4 0 16)));
      v_6 <- eval (add (concat (expression.bv_nat 1 0) (extract v_3 16 32)) (concat (expression.bv_nat 1 0) (extract v_4 16 32)));
      v_7 <- eval (add (concat (expression.bv_nat 1 0) (extract v_3 32 48)) (concat (expression.bv_nat 1 0) (extract v_4 32 48)));
      v_8 <- eval (add (concat (expression.bv_nat 1 0) (extract v_3 48 64)) (concat (expression.bv_nat 1 0) (extract v_4 48 64)));
      v_9 <- eval (add (concat (expression.bv_nat 1 0) (extract v_3 64 80)) (concat (expression.bv_nat 1 0) (extract v_4 64 80)));
      v_10 <- eval (add (concat (expression.bv_nat 1 0) (extract v_3 80 96)) (concat (expression.bv_nat 1 0) (extract v_4 80 96)));
      v_11 <- eval (add (concat (expression.bv_nat 1 0) (extract v_3 96 112)) (concat (expression.bv_nat 1 0) (extract v_4 96 112)));
      v_12 <- eval (add (concat (expression.bv_nat 1 0) (extract v_3 112 128)) (concat (expression.bv_nat 1 0) (extract v_4 112 128)));
      setRegister (lhs.of_reg xmm_2) (concat (mux (isBitSet v_5 0) (expression.bv_nat 16 65535) (extract v_5 1 17)) (concat (mux (isBitSet v_6 0) (expression.bv_nat 16 65535) (extract v_6 1 17)) (concat (mux (isBitSet v_7 0) (expression.bv_nat 16 65535) (extract v_7 1 17)) (concat (mux (isBitSet v_8 0) (expression.bv_nat 16 65535) (extract v_8 1 17)) (concat (mux (isBitSet v_9 0) (expression.bv_nat 16 65535) (extract v_9 1 17)) (concat (mux (isBitSet v_10 0) (expression.bv_nat 16 65535) (extract v_10 1 17)) (concat (mux (isBitSet v_11 0) (expression.bv_nat 16 65535) (extract v_11 1 17)) (mux (isBitSet v_12 0) (expression.bv_nat 16 65535) (extract v_12 1 17)))))))));
      pure ()
    pat_end;
    pattern fun (ymm_0 : reg (bv 256)) (ymm_1 : reg (bv 256)) (ymm_2 : reg (bv 256)) => do
      v_3 <- getRegister (lhs.of_reg ymm_1);
      v_4 <- getRegister (lhs.of_reg ymm_0);
      v_5 <- eval (add (concat (expression.bv_nat 1 0) (extract v_3 0 16)) (concat (expression.bv_nat 1 0) (extract v_4 0 16)));
      v_6 <- eval (add (concat (expression.bv_nat 1 0) (extract v_3 16 32)) (concat (expression.bv_nat 1 0) (extract v_4 16 32)));
      v_7 <- eval (add (concat (expression.bv_nat 1 0) (extract v_3 32 48)) (concat (expression.bv_nat 1 0) (extract v_4 32 48)));
      v_8 <- eval (add (concat (expression.bv_nat 1 0) (extract v_3 48 64)) (concat (expression.bv_nat 1 0) (extract v_4 48 64)));
      v_9 <- eval (add (concat (expression.bv_nat 1 0) (extract v_3 64 80)) (concat (expression.bv_nat 1 0) (extract v_4 64 80)));
      v_10 <- eval (add (concat (expression.bv_nat 1 0) (extract v_3 80 96)) (concat (expression.bv_nat 1 0) (extract v_4 80 96)));
      v_11 <- eval (add (concat (expression.bv_nat 1 0) (extract v_3 96 112)) (concat (expression.bv_nat 1 0) (extract v_4 96 112)));
      v_12 <- eval (add (concat (expression.bv_nat 1 0) (extract v_3 112 128)) (concat (expression.bv_nat 1 0) (extract v_4 112 128)));
      v_13 <- eval (add (concat (expression.bv_nat 1 0) (extract v_3 128 144)) (concat (expression.bv_nat 1 0) (extract v_4 128 144)));
      v_14 <- eval (add (concat (expression.bv_nat 1 0) (extract v_3 144 160)) (concat (expression.bv_nat 1 0) (extract v_4 144 160)));
      v_15 <- eval (add (concat (expression.bv_nat 1 0) (extract v_3 160 176)) (concat (expression.bv_nat 1 0) (extract v_4 160 176)));
      v_16 <- eval (add (concat (expression.bv_nat 1 0) (extract v_3 176 192)) (concat (expression.bv_nat 1 0) (extract v_4 176 192)));
      v_17 <- eval (add (concat (expression.bv_nat 1 0) (extract v_3 192 208)) (concat (expression.bv_nat 1 0) (extract v_4 192 208)));
      v_18 <- eval (add (concat (expression.bv_nat 1 0) (extract v_3 208 224)) (concat (expression.bv_nat 1 0) (extract v_4 208 224)));
      v_19 <- eval (add (concat (expression.bv_nat 1 0) (extract v_3 224 240)) (concat (expression.bv_nat 1 0) (extract v_4 224 240)));
      v_20 <- eval (add (concat (expression.bv_nat 1 0) (extract v_3 240 256)) (concat (expression.bv_nat 1 0) (extract v_4 240 256)));
      setRegister (lhs.of_reg ymm_2) (concat (mux (isBitSet v_5 0) (expression.bv_nat 16 65535) (extract v_5 1 17)) (concat (mux (isBitSet v_6 0) (expression.bv_nat 16 65535) (extract v_6 1 17)) (concat (mux (isBitSet v_7 0) (expression.bv_nat 16 65535) (extract v_7 1 17)) (concat (mux (isBitSet v_8 0) (expression.bv_nat 16 65535) (extract v_8 1 17)) (concat (mux (isBitSet v_9 0) (expression.bv_nat 16 65535) (extract v_9 1 17)) (concat (mux (isBitSet v_10 0) (expression.bv_nat 16 65535) (extract v_10 1 17)) (concat (mux (isBitSet v_11 0) (expression.bv_nat 16 65535) (extract v_11 1 17)) (concat (mux (isBitSet v_12 0) (expression.bv_nat 16 65535) (extract v_12 1 17)) (concat (mux (isBitSet v_13 0) (expression.bv_nat 16 65535) (extract v_13 1 17)) (concat (mux (isBitSet v_14 0) (expression.bv_nat 16 65535) (extract v_14 1 17)) (concat (mux (isBitSet v_15 0) (expression.bv_nat 16 65535) (extract v_15 1 17)) (concat (mux (isBitSet v_16 0) (expression.bv_nat 16 65535) (extract v_16 1 17)) (concat (mux (isBitSet v_17 0) (expression.bv_nat 16 65535) (extract v_17 1 17)) (concat (mux (isBitSet v_18 0) (expression.bv_nat 16 65535) (extract v_18 1 17)) (concat (mux (isBitSet v_19 0) (expression.bv_nat 16 65535) (extract v_19 1 17)) (mux (isBitSet v_20 0) (expression.bv_nat 16 65535) (extract v_20 1 17)))))))))))))))));
      pure ()
    pat_end
