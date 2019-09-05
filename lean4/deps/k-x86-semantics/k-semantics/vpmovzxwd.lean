def vpmovzxwd1 : instruction :=
  definst "vpmovzxwd" $ do
    pattern fun (v_2836 : reg (bv 128)) (v_2837 : reg (bv 128)) => do
      v_5910 <- getRegister v_2836;
      setRegister (lhs.of_reg v_2837) (concat (expression.bv_nat 16 0) (concat (extract v_5910 64 80) (concat (expression.bv_nat 16 0) (concat (extract v_5910 80 96) (concat (expression.bv_nat 16 0) (concat (extract v_5910 96 112) (concat (expression.bv_nat 16 0) (extract v_5910 112 128))))))));
      pure ()
    pat_end;
    pattern fun (v_2846 : reg (bv 128)) (v_2845 : reg (bv 256)) => do
      v_5927 <- getRegister v_2846;
      setRegister (lhs.of_reg v_2845) (concat (expression.bv_nat 16 0) (concat (extract v_5927 0 16) (concat (expression.bv_nat 16 0) (concat (extract v_5927 16 32) (concat (expression.bv_nat 16 0) (concat (extract v_5927 32 48) (concat (expression.bv_nat 16 0) (concat (extract v_5927 48 64) (concat (expression.bv_nat 16 0) (concat (extract v_5927 64 80) (concat (expression.bv_nat 16 0) (concat (extract v_5927 80 96) (concat (expression.bv_nat 16 0) (concat (extract v_5927 96 112) (concat (expression.bv_nat 16 0) (extract v_5927 112 128))))))))))))))));
      pure ()
    pat_end;
    pattern fun (v_2831 : Mem) (v_2832 : reg (bv 128)) => do
      v_12281 <- evaluateAddress v_2831;
      v_12282 <- load v_12281 8;
      setRegister (lhs.of_reg v_2832) (concat (expression.bv_nat 16 0) (concat (extract v_12282 0 16) (concat (expression.bv_nat 16 0) (concat (extract v_12282 16 32) (concat (expression.bv_nat 16 0) (concat (extract v_12282 32 48) (concat (expression.bv_nat 16 0) (extract v_12282 48 64))))))));
      pure ()
    pat_end;
    pattern fun (v_2840 : Mem) (v_2841 : reg (bv 256)) => do
      v_12295 <- evaluateAddress v_2840;
      v_12296 <- load v_12295 16;
      setRegister (lhs.of_reg v_2841) (concat (expression.bv_nat 16 0) (concat (extract v_12296 0 16) (concat (expression.bv_nat 16 0) (concat (extract v_12296 16 32) (concat (expression.bv_nat 16 0) (concat (extract v_12296 32 48) (concat (expression.bv_nat 16 0) (concat (extract v_12296 48 64) (concat (expression.bv_nat 16 0) (concat (extract v_12296 64 80) (concat (expression.bv_nat 16 0) (concat (extract v_12296 80 96) (concat (expression.bv_nat 16 0) (concat (extract v_12296 96 112) (concat (expression.bv_nat 16 0) (extract v_12296 112 128))))))))))))))));
      pure ()
    pat_end
