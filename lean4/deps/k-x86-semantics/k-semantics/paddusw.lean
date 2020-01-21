def paddusw : instruction :=
  definst "paddusw" $ do
    pattern fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) => do
      v_2 <- getRegister (lhs.of_reg xmm_1);
      v_3 <- evaluateAddress mem_0;
      v_4 <- load v_3 16;
      v_5 <- eval (add (concat (expression.bv_nat 1 0) (extract v_2 0 16)) (concat (expression.bv_nat 1 0) (extract v_4 0 16)));
      v_6 <- eval (add (concat (expression.bv_nat 1 0) (extract v_2 16 32)) (concat (expression.bv_nat 1 0) (extract v_4 16 32)));
      v_7 <- eval (add (concat (expression.bv_nat 1 0) (extract v_2 32 48)) (concat (expression.bv_nat 1 0) (extract v_4 32 48)));
      v_8 <- eval (add (concat (expression.bv_nat 1 0) (extract v_2 48 64)) (concat (expression.bv_nat 1 0) (extract v_4 48 64)));
      v_9 <- eval (add (concat (expression.bv_nat 1 0) (extract v_2 64 80)) (concat (expression.bv_nat 1 0) (extract v_4 64 80)));
      v_10 <- eval (add (concat (expression.bv_nat 1 0) (extract v_2 80 96)) (concat (expression.bv_nat 1 0) (extract v_4 80 96)));
      v_11 <- eval (add (concat (expression.bv_nat 1 0) (extract v_2 96 112)) (concat (expression.bv_nat 1 0) (extract v_4 96 112)));
      v_12 <- eval (add (concat (expression.bv_nat 1 0) (extract v_2 112 128)) (concat (expression.bv_nat 1 0) (extract v_4 112 128)));
      setRegister (lhs.of_reg xmm_1) (concat (mux (isBitSet v_5 0) (expression.bv_nat 16 65535) (extract v_5 1 17)) (concat (mux (isBitSet v_6 0) (expression.bv_nat 16 65535) (extract v_6 1 17)) (concat (mux (isBitSet v_7 0) (expression.bv_nat 16 65535) (extract v_7 1 17)) (concat (mux (isBitSet v_8 0) (expression.bv_nat 16 65535) (extract v_8 1 17)) (concat (mux (isBitSet v_9 0) (expression.bv_nat 16 65535) (extract v_9 1 17)) (concat (mux (isBitSet v_10 0) (expression.bv_nat 16 65535) (extract v_10 1 17)) (concat (mux (isBitSet v_11 0) (expression.bv_nat 16 65535) (extract v_11 1 17)) (mux (isBitSet v_12 0) (expression.bv_nat 16 65535) (extract v_12 1 17)))))))));
      pure ()
    pat_end;
    pattern fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) => do
      v_2 <- getRegister (lhs.of_reg xmm_1);
      v_3 <- getRegister (lhs.of_reg xmm_0);
      v_4 <- eval (add (concat (expression.bv_nat 1 0) (extract v_2 0 16)) (concat (expression.bv_nat 1 0) (extract v_3 0 16)));
      v_5 <- eval (add (concat (expression.bv_nat 1 0) (extract v_2 16 32)) (concat (expression.bv_nat 1 0) (extract v_3 16 32)));
      v_6 <- eval (add (concat (expression.bv_nat 1 0) (extract v_2 32 48)) (concat (expression.bv_nat 1 0) (extract v_3 32 48)));
      v_7 <- eval (add (concat (expression.bv_nat 1 0) (extract v_2 48 64)) (concat (expression.bv_nat 1 0) (extract v_3 48 64)));
      v_8 <- eval (add (concat (expression.bv_nat 1 0) (extract v_2 64 80)) (concat (expression.bv_nat 1 0) (extract v_3 64 80)));
      v_9 <- eval (add (concat (expression.bv_nat 1 0) (extract v_2 80 96)) (concat (expression.bv_nat 1 0) (extract v_3 80 96)));
      v_10 <- eval (add (concat (expression.bv_nat 1 0) (extract v_2 96 112)) (concat (expression.bv_nat 1 0) (extract v_3 96 112)));
      v_11 <- eval (add (concat (expression.bv_nat 1 0) (extract v_2 112 128)) (concat (expression.bv_nat 1 0) (extract v_3 112 128)));
      setRegister (lhs.of_reg xmm_1) (concat (mux (isBitSet v_4 0) (expression.bv_nat 16 65535) (extract v_4 1 17)) (concat (mux (isBitSet v_5 0) (expression.bv_nat 16 65535) (extract v_5 1 17)) (concat (mux (isBitSet v_6 0) (expression.bv_nat 16 65535) (extract v_6 1 17)) (concat (mux (isBitSet v_7 0) (expression.bv_nat 16 65535) (extract v_7 1 17)) (concat (mux (isBitSet v_8 0) (expression.bv_nat 16 65535) (extract v_8 1 17)) (concat (mux (isBitSet v_9 0) (expression.bv_nat 16 65535) (extract v_9 1 17)) (concat (mux (isBitSet v_10 0) (expression.bv_nat 16 65535) (extract v_10 1 17)) (mux (isBitSet v_11 0) (expression.bv_nat 16 65535) (extract v_11 1 17)))))))));
      pure ()
    pat_end
