def vpmovzxdq1 : instruction :=
  definst "vpmovzxdq" $ do
    pattern fun (v_2845 : reg (bv 128)) (v_2846 : reg (bv 128)) => do
      v_5909 <- getRegister v_2845;
      setRegister (lhs.of_reg v_2846) (concat (expression.bv_nat 32 0) (concat (extract v_5909 64 96) (concat (expression.bv_nat 32 0) (extract v_5909 96 128))));
      pure ()
    pat_end;
    pattern fun (v_2855 : reg (bv 128)) (v_2854 : reg (bv 256)) => do
      v_5920 <- getRegister v_2855;
      setRegister (lhs.of_reg v_2854) (concat (expression.bv_nat 32 0) (concat (extract v_5920 0 32) (concat (expression.bv_nat 32 0) (concat (extract v_5920 32 64) (concat (expression.bv_nat 32 0) (concat (extract v_5920 64 96) (concat (expression.bv_nat 32 0) (extract v_5920 96 128))))))));
      pure ()
    pat_end;
    pattern fun (v_2840 : Mem) (v_2841 : reg (bv 128)) => do
      v_12286 <- evaluateAddress v_2840;
      v_12287 <- load v_12286 8;
      setRegister (lhs.of_reg v_2841) (concat (expression.bv_nat 32 0) (concat (extract v_12287 0 32) (concat (expression.bv_nat 32 0) (extract v_12287 32 64))));
      pure ()
    pat_end;
    pattern fun (v_2849 : Mem) (v_2850 : reg (bv 256)) => do
      v_12294 <- evaluateAddress v_2849;
      v_12295 <- load v_12294 16;
      setRegister (lhs.of_reg v_2850) (concat (expression.bv_nat 32 0) (concat (extract v_12295 0 32) (concat (expression.bv_nat 32 0) (concat (extract v_12295 32 64) (concat (expression.bv_nat 32 0) (concat (extract v_12295 64 96) (concat (expression.bv_nat 32 0) (extract v_12295 96 128))))))));
      pure ()
    pat_end
