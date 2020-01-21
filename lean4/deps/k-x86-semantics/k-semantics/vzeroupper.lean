def vzeroupper : instruction :=
  definst "vzeroupper" $ do
    pattern fun => do
      v_0 <- getRegister ymm9;
      v_1 <- getRegister ymm8;
      v_2 <- getRegister ymm7;
      v_3 <- getRegister ymm6;
      v_4 <- getRegister ymm5;
      v_5 <- getRegister ymm4;
      v_6 <- getRegister ymm3;
      v_7 <- getRegister ymm2;
      v_8 <- getRegister ymm15;
      v_9 <- getRegister ymm14;
      v_10 <- getRegister ymm13;
      v_11 <- getRegister ymm12;
      v_12 <- getRegister ymm11;
      v_13 <- getRegister ymm10;
      v_14 <- getRegister ymm1;
      v_15 <- getRegister ymm0;
      setRegister ymm0 (concat (expression.bv_nat 128 0) (extract v_15 128 256));
      setRegister ymm1 (concat (expression.bv_nat 128 0) (extract v_14 128 256));
      setRegister ymm10 (concat (expression.bv_nat 128 0) (extract v_13 128 256));
      setRegister ymm11 (concat (expression.bv_nat 128 0) (extract v_12 128 256));
      setRegister ymm12 (concat (expression.bv_nat 128 0) (extract v_11 128 256));
      setRegister ymm13 (concat (expression.bv_nat 128 0) (extract v_10 128 256));
      setRegister ymm14 (concat (expression.bv_nat 128 0) (extract v_9 128 256));
      setRegister ymm15 (concat (expression.bv_nat 128 0) (extract v_8 128 256));
      setRegister ymm2 (concat (expression.bv_nat 128 0) (extract v_7 128 256));
      setRegister ymm3 (concat (expression.bv_nat 128 0) (extract v_6 128 256));
      setRegister ymm4 (concat (expression.bv_nat 128 0) (extract v_5 128 256));
      setRegister ymm5 (concat (expression.bv_nat 128 0) (extract v_4 128 256));
      setRegister ymm6 (concat (expression.bv_nat 128 0) (extract v_3 128 256));
      setRegister ymm7 (concat (expression.bv_nat 128 0) (extract v_2 128 256));
      setRegister ymm8 (concat (expression.bv_nat 128 0) (extract v_1 128 256));
      setRegister ymm9 (concat (expression.bv_nat 128 0) (extract v_0 128 256));
      pure ()
    pat_end
