def paddusb1 : instruction :=
  definst "paddusb" $ do
    pattern fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) => do
      v_2 <- getRegister xmm_1;
      v_3 <- evaluateAddress mem_0;
      v_4 <- load v_3 16;
      v_5 <- eval (add (concat (expression.bv_nat 1 0) (extract v_2 0 8)) (concat (expression.bv_nat 1 0) (extract v_4 0 8)));
      v_6 <- eval (add (concat (expression.bv_nat 1 0) (extract v_2 8 16)) (concat (expression.bv_nat 1 0) (extract v_4 8 16)));
      v_7 <- eval (add (concat (expression.bv_nat 1 0) (extract v_2 16 24)) (concat (expression.bv_nat 1 0) (extract v_4 16 24)));
      v_8 <- eval (add (concat (expression.bv_nat 1 0) (extract v_2 24 32)) (concat (expression.bv_nat 1 0) (extract v_4 24 32)));
      v_9 <- eval (add (concat (expression.bv_nat 1 0) (extract v_2 32 40)) (concat (expression.bv_nat 1 0) (extract v_4 32 40)));
      v_10 <- eval (add (concat (expression.bv_nat 1 0) (extract v_2 40 48)) (concat (expression.bv_nat 1 0) (extract v_4 40 48)));
      v_11 <- eval (add (concat (expression.bv_nat 1 0) (extract v_2 48 56)) (concat (expression.bv_nat 1 0) (extract v_4 48 56)));
      v_12 <- eval (add (concat (expression.bv_nat 1 0) (extract v_2 56 64)) (concat (expression.bv_nat 1 0) (extract v_4 56 64)));
      v_13 <- eval (add (concat (expression.bv_nat 1 0) (extract v_2 64 72)) (concat (expression.bv_nat 1 0) (extract v_4 64 72)));
      v_14 <- eval (add (concat (expression.bv_nat 1 0) (extract v_2 72 80)) (concat (expression.bv_nat 1 0) (extract v_4 72 80)));
      v_15 <- eval (add (concat (expression.bv_nat 1 0) (extract v_2 80 88)) (concat (expression.bv_nat 1 0) (extract v_4 80 88)));
      v_16 <- eval (add (concat (expression.bv_nat 1 0) (extract v_2 88 96)) (concat (expression.bv_nat 1 0) (extract v_4 88 96)));
      v_17 <- eval (add (concat (expression.bv_nat 1 0) (extract v_2 96 104)) (concat (expression.bv_nat 1 0) (extract v_4 96 104)));
      v_18 <- eval (add (concat (expression.bv_nat 1 0) (extract v_2 104 112)) (concat (expression.bv_nat 1 0) (extract v_4 104 112)));
      v_19 <- eval (add (concat (expression.bv_nat 1 0) (extract v_2 112 120)) (concat (expression.bv_nat 1 0) (extract v_4 112 120)));
      v_20 <- eval (add (concat (expression.bv_nat 1 0) (extract v_2 120 128)) (concat (expression.bv_nat 1 0) (extract v_4 120 128)));
      setRegister (lhs.of_reg xmm_1) (concat (mux (isBitSet v_5 0) (expression.bv_nat 8 255) (extract v_5 1 9)) (concat (mux (isBitSet v_6 0) (expression.bv_nat 8 255) (extract v_6 1 9)) (concat (mux (isBitSet v_7 0) (expression.bv_nat 8 255) (extract v_7 1 9)) (concat (mux (isBitSet v_8 0) (expression.bv_nat 8 255) (extract v_8 1 9)) (concat (mux (isBitSet v_9 0) (expression.bv_nat 8 255) (extract v_9 1 9)) (concat (mux (isBitSet v_10 0) (expression.bv_nat 8 255) (extract v_10 1 9)) (concat (mux (isBitSet v_11 0) (expression.bv_nat 8 255) (extract v_11 1 9)) (concat (mux (isBitSet v_12 0) (expression.bv_nat 8 255) (extract v_12 1 9)) (concat (mux (isBitSet v_13 0) (expression.bv_nat 8 255) (extract v_13 1 9)) (concat (mux (isBitSet v_14 0) (expression.bv_nat 8 255) (extract v_14 1 9)) (concat (mux (isBitSet v_15 0) (expression.bv_nat 8 255) (extract v_15 1 9)) (concat (mux (isBitSet v_16 0) (expression.bv_nat 8 255) (extract v_16 1 9)) (concat (mux (isBitSet v_17 0) (expression.bv_nat 8 255) (extract v_17 1 9)) (concat (mux (isBitSet v_18 0) (expression.bv_nat 8 255) (extract v_18 1 9)) (concat (mux (isBitSet v_19 0) (expression.bv_nat 8 255) (extract v_19 1 9)) (mux (isBitSet v_20 0) (expression.bv_nat 8 255) (extract v_20 1 9)))))))))))))))));
      pure ()
    pat_end;
    pattern fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) => do
      v_2 <- getRegister xmm_1;
      v_3 <- getRegister xmm_0;
      v_4 <- eval (add (concat (expression.bv_nat 1 0) (extract v_2 0 8)) (concat (expression.bv_nat 1 0) (extract v_3 0 8)));
      v_5 <- eval (add (concat (expression.bv_nat 1 0) (extract v_2 8 16)) (concat (expression.bv_nat 1 0) (extract v_3 8 16)));
      v_6 <- eval (add (concat (expression.bv_nat 1 0) (extract v_2 16 24)) (concat (expression.bv_nat 1 0) (extract v_3 16 24)));
      v_7 <- eval (add (concat (expression.bv_nat 1 0) (extract v_2 24 32)) (concat (expression.bv_nat 1 0) (extract v_3 24 32)));
      v_8 <- eval (add (concat (expression.bv_nat 1 0) (extract v_2 32 40)) (concat (expression.bv_nat 1 0) (extract v_3 32 40)));
      v_9 <- eval (add (concat (expression.bv_nat 1 0) (extract v_2 40 48)) (concat (expression.bv_nat 1 0) (extract v_3 40 48)));
      v_10 <- eval (add (concat (expression.bv_nat 1 0) (extract v_2 48 56)) (concat (expression.bv_nat 1 0) (extract v_3 48 56)));
      v_11 <- eval (add (concat (expression.bv_nat 1 0) (extract v_2 56 64)) (concat (expression.bv_nat 1 0) (extract v_3 56 64)));
      v_12 <- eval (add (concat (expression.bv_nat 1 0) (extract v_2 64 72)) (concat (expression.bv_nat 1 0) (extract v_3 64 72)));
      v_13 <- eval (add (concat (expression.bv_nat 1 0) (extract v_2 72 80)) (concat (expression.bv_nat 1 0) (extract v_3 72 80)));
      v_14 <- eval (add (concat (expression.bv_nat 1 0) (extract v_2 80 88)) (concat (expression.bv_nat 1 0) (extract v_3 80 88)));
      v_15 <- eval (add (concat (expression.bv_nat 1 0) (extract v_2 88 96)) (concat (expression.bv_nat 1 0) (extract v_3 88 96)));
      v_16 <- eval (add (concat (expression.bv_nat 1 0) (extract v_2 96 104)) (concat (expression.bv_nat 1 0) (extract v_3 96 104)));
      v_17 <- eval (add (concat (expression.bv_nat 1 0) (extract v_2 104 112)) (concat (expression.bv_nat 1 0) (extract v_3 104 112)));
      v_18 <- eval (add (concat (expression.bv_nat 1 0) (extract v_2 112 120)) (concat (expression.bv_nat 1 0) (extract v_3 112 120)));
      v_19 <- eval (add (concat (expression.bv_nat 1 0) (extract v_2 120 128)) (concat (expression.bv_nat 1 0) (extract v_3 120 128)));
      setRegister (lhs.of_reg xmm_1) (concat (mux (isBitSet v_4 0) (expression.bv_nat 8 255) (extract v_4 1 9)) (concat (mux (isBitSet v_5 0) (expression.bv_nat 8 255) (extract v_5 1 9)) (concat (mux (isBitSet v_6 0) (expression.bv_nat 8 255) (extract v_6 1 9)) (concat (mux (isBitSet v_7 0) (expression.bv_nat 8 255) (extract v_7 1 9)) (concat (mux (isBitSet v_8 0) (expression.bv_nat 8 255) (extract v_8 1 9)) (concat (mux (isBitSet v_9 0) (expression.bv_nat 8 255) (extract v_9 1 9)) (concat (mux (isBitSet v_10 0) (expression.bv_nat 8 255) (extract v_10 1 9)) (concat (mux (isBitSet v_11 0) (expression.bv_nat 8 255) (extract v_11 1 9)) (concat (mux (isBitSet v_12 0) (expression.bv_nat 8 255) (extract v_12 1 9)) (concat (mux (isBitSet v_13 0) (expression.bv_nat 8 255) (extract v_13 1 9)) (concat (mux (isBitSet v_14 0) (expression.bv_nat 8 255) (extract v_14 1 9)) (concat (mux (isBitSet v_15 0) (expression.bv_nat 8 255) (extract v_15 1 9)) (concat (mux (isBitSet v_16 0) (expression.bv_nat 8 255) (extract v_16 1 9)) (concat (mux (isBitSet v_17 0) (expression.bv_nat 8 255) (extract v_17 1 9)) (concat (mux (isBitSet v_18 0) (expression.bv_nat 8 255) (extract v_18 1 9)) (mux (isBitSet v_19 0) (expression.bv_nat 8 255) (extract v_19 1 9)))))))))))))))));
      pure ()
    pat_end
