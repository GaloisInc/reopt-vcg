def vzeroupper1 : instruction :=
  definst "vzeroupper" $ do
    pattern fun => do
      v_3856 <- getRegister ymm9;
      v_3859 <- getRegister ymm2;
      v_3862 <- getRegister ymm12;
      v_3865 <- getRegister ymm1;
      v_3868 <- getRegister ymm13;
      v_3871 <- getRegister ymm4;
      v_3874 <- getRegister ymm10;
      v_3877 <- getRegister ymm3;
      v_3880 <- getRegister ymm11;
      v_3883 <- getRegister ymm6;
      v_3886 <- getRegister ymm5;
      v_3889 <- getRegister ymm8;
      v_3892 <- getRegister ymm14;
      v_3895 <- getRegister ymm0;
      v_3898 <- getRegister ymm7;
      v_3901 <- getRegister ymm15;
      setRegister ymm15 (concat (expression.bv_nat 128 0) (extract v_3901 128 256));
      setRegister ymm7 (concat (expression.bv_nat 128 0) (extract v_3898 128 256));
      setRegister ymm0 (concat (expression.bv_nat 128 0) (extract v_3895 128 256));
      setRegister ymm14 (concat (expression.bv_nat 128 0) (extract v_3892 128 256));
      setRegister ymm8 (concat (expression.bv_nat 128 0) (extract v_3889 128 256));
      setRegister ymm5 (concat (expression.bv_nat 128 0) (extract v_3886 128 256));
      setRegister ymm6 (concat (expression.bv_nat 128 0) (extract v_3883 128 256));
      setRegister ymm11 (concat (expression.bv_nat 128 0) (extract v_3880 128 256));
      setRegister ymm3 (concat (expression.bv_nat 128 0) (extract v_3877 128 256));
      setRegister ymm10 (concat (expression.bv_nat 128 0) (extract v_3874 128 256));
      setRegister ymm4 (concat (expression.bv_nat 128 0) (extract v_3871 128 256));
      setRegister ymm13 (concat (expression.bv_nat 128 0) (extract v_3868 128 256));
      setRegister ymm1 (concat (expression.bv_nat 128 0) (extract v_3865 128 256));
      setRegister ymm12 (concat (expression.bv_nat 128 0) (extract v_3862 128 256));
      setRegister ymm2 (concat (expression.bv_nat 128 0) (extract v_3859 128 256));
      setRegister ymm9 (concat (expression.bv_nat 128 0) (extract v_3856 128 256));
      pure ()
    pat_end
