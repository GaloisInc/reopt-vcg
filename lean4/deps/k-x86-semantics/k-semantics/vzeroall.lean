def vzeroall1 : instruction :=
  definst "vzeroall" $ do
    pattern fun => do
      setRegister ymm15 (expression.bv_nat 256 0);
      setRegister ymm7 (expression.bv_nat 256 0);
      setRegister ymm0 (expression.bv_nat 256 0);
      setRegister ymm14 (expression.bv_nat 256 0);
      setRegister ymm8 (expression.bv_nat 256 0);
      setRegister ymm5 (expression.bv_nat 256 0);
      setRegister ymm6 (expression.bv_nat 256 0);
      setRegister ymm11 (expression.bv_nat 256 0);
      setRegister ymm3 (expression.bv_nat 256 0);
      setRegister ymm10 (expression.bv_nat 256 0);
      setRegister ymm4 (expression.bv_nat 256 0);
      setRegister ymm13 (expression.bv_nat 256 0);
      setRegister ymm1 (expression.bv_nat 256 0);
      setRegister ymm12 (expression.bv_nat 256 0);
      setRegister ymm2 (expression.bv_nat 256 0);
      setRegister ymm9 (expression.bv_nat 256 0);
      pure ()
    pat_end
