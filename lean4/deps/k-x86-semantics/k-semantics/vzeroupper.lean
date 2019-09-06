def vzeroupper1 : instruction :=
  definst "vzeroupper" $ do
    pattern fun => do
      v_7718 <- getRegister ymm9;
      v_7721 <- getRegister ymm8;
      v_7724 <- getRegister ymm7;
      v_7727 <- getRegister ymm6;
      v_7730 <- getRegister ymm5;
      v_7733 <- getRegister ymm4;
      v_7736 <- getRegister ymm3;
      v_7739 <- getRegister ymm2;
      v_7742 <- getRegister ymm15;
      v_7745 <- getRegister ymm14;
      v_7748 <- getRegister ymm13;
      v_7751 <- getRegister ymm12;
      v_7754 <- getRegister ymm11;
      v_7757 <- getRegister ymm10;
      v_7760 <- getRegister ymm1;
      v_7763 <- getRegister ymm0;
      setRegister ymm0 (concat (expression.bv_nat 128 0) (extract v_7763 128 256));
      setRegister ymm1 (concat (expression.bv_nat 128 0) (extract v_7760 128 256));
      setRegister ymm10 (concat (expression.bv_nat 128 0) (extract v_7757 128 256));
      setRegister ymm11 (concat (expression.bv_nat 128 0) (extract v_7754 128 256));
      setRegister ymm12 (concat (expression.bv_nat 128 0) (extract v_7751 128 256));
      setRegister ymm13 (concat (expression.bv_nat 128 0) (extract v_7748 128 256));
      setRegister ymm14 (concat (expression.bv_nat 128 0) (extract v_7745 128 256));
      setRegister ymm15 (concat (expression.bv_nat 128 0) (extract v_7742 128 256));
      setRegister ymm2 (concat (expression.bv_nat 128 0) (extract v_7739 128 256));
      setRegister ymm3 (concat (expression.bv_nat 128 0) (extract v_7736 128 256));
      setRegister ymm4 (concat (expression.bv_nat 128 0) (extract v_7733 128 256));
      setRegister ymm5 (concat (expression.bv_nat 128 0) (extract v_7730 128 256));
      setRegister ymm6 (concat (expression.bv_nat 128 0) (extract v_7727 128 256));
      setRegister ymm7 (concat (expression.bv_nat 128 0) (extract v_7724 128 256));
      setRegister ymm8 (concat (expression.bv_nat 128 0) (extract v_7721 128 256));
      setRegister ymm9 (concat (expression.bv_nat 128 0) (extract v_7718 128 256));
      pure ()
    pat_end
