def vzeroupper : instruction :=
  definst "vzeroupper" $ do
    pattern do
      v_0 <- getRegister ymm9;
      (v_1 : expression (bv 128)) <- eval (extract v_0 128 256);
      v_2 <- getRegister ymm8;
      (v_3 : expression (bv 128)) <- eval (extract v_2 128 256);
      v_4 <- getRegister ymm7;
      (v_5 : expression (bv 128)) <- eval (extract v_4 128 256);
      v_6 <- getRegister ymm6;
      (v_7 : expression (bv 128)) <- eval (extract v_6 128 256);
      v_8 <- getRegister ymm5;
      (v_9 : expression (bv 128)) <- eval (extract v_8 128 256);
      v_10 <- getRegister ymm4;
      (v_11 : expression (bv 128)) <- eval (extract v_10 128 256);
      v_12 <- getRegister ymm3;
      (v_13 : expression (bv 128)) <- eval (extract v_12 128 256);
      v_14 <- getRegister ymm2;
      (v_15 : expression (bv 128)) <- eval (extract v_14 128 256);
      v_16 <- getRegister ymm15;
      (v_17 : expression (bv 128)) <- eval (extract v_16 128 256);
      v_18 <- getRegister ymm14;
      (v_19 : expression (bv 128)) <- eval (extract v_18 128 256);
      v_20 <- getRegister ymm13;
      (v_21 : expression (bv 128)) <- eval (extract v_20 128 256);
      v_22 <- getRegister ymm12;
      (v_23 : expression (bv 128)) <- eval (extract v_22 128 256);
      v_24 <- getRegister ymm11;
      (v_25 : expression (bv 128)) <- eval (extract v_24 128 256);
      v_26 <- getRegister ymm10;
      (v_27 : expression (bv 128)) <- eval (extract v_26 128 256);
      v_28 <- getRegister ymm1;
      (v_29 : expression (bv 128)) <- eval (extract v_28 128 256);
      v_30 <- getRegister ymm0;
      (v_31 : expression (bv 128)) <- eval (extract v_30 128 256);
      setRegister ymm0 (concat (expression.bv_nat 128 0) v_31);
      setRegister ymm1 (concat (expression.bv_nat 128 0) v_29);
      setRegister ymm10 (concat (expression.bv_nat 128 0) v_27);
      setRegister ymm11 (concat (expression.bv_nat 128 0) v_25);
      setRegister ymm12 (concat (expression.bv_nat 128 0) v_23);
      setRegister ymm13 (concat (expression.bv_nat 128 0) v_21);
      setRegister ymm14 (concat (expression.bv_nat 128 0) v_19);
      setRegister ymm15 (concat (expression.bv_nat 128 0) v_17);
      setRegister ymm2 (concat (expression.bv_nat 128 0) v_15);
      setRegister ymm3 (concat (expression.bv_nat 128 0) v_13);
      setRegister ymm4 (concat (expression.bv_nat 128 0) v_11);
      setRegister ymm5 (concat (expression.bv_nat 128 0) v_9);
      setRegister ymm6 (concat (expression.bv_nat 128 0) v_7);
      setRegister ymm7 (concat (expression.bv_nat 128 0) v_5);
      setRegister ymm8 (concat (expression.bv_nat 128 0) v_3);
      setRegister ymm9 (concat (expression.bv_nat 128 0) v_1);
      pure ()
    pat_end
