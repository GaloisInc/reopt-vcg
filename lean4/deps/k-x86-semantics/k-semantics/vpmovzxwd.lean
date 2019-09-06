def vpmovzxwd1 : instruction :=
  definst "vpmovzxwd" $ do
    pattern fun (v_2863 : reg (bv 128)) (v_2864 : reg (bv 128)) => do
      v_5937 <- getRegister v_2863;
      setRegister (lhs.of_reg v_2864) (concat (expression.bv_nat 16 0) (concat (extract v_5937 64 80) (concat (expression.bv_nat 16 0) (concat (extract v_5937 80 96) (concat (expression.bv_nat 16 0) (concat (extract v_5937 96 112) (concat (expression.bv_nat 16 0) (extract v_5937 112 128))))))));
      pure ()
    pat_end;
    pattern fun (v_2873 : reg (bv 128)) (v_2872 : reg (bv 256)) => do
      v_5954 <- getRegister v_2873;
      setRegister (lhs.of_reg v_2872) (concat (expression.bv_nat 16 0) (concat (extract v_5954 0 16) (concat (expression.bv_nat 16 0) (concat (extract v_5954 16 32) (concat (expression.bv_nat 16 0) (concat (extract v_5954 32 48) (concat (expression.bv_nat 16 0) (concat (extract v_5954 48 64) (concat (expression.bv_nat 16 0) (concat (extract v_5954 64 80) (concat (expression.bv_nat 16 0) (concat (extract v_5954 80 96) (concat (expression.bv_nat 16 0) (concat (extract v_5954 96 112) (concat (expression.bv_nat 16 0) (extract v_5954 112 128))))))))))))))));
      pure ()
    pat_end;
    pattern fun (v_2858 : Mem) (v_2859 : reg (bv 128)) => do
      v_12308 <- evaluateAddress v_2858;
      v_12309 <- load v_12308 8;
      setRegister (lhs.of_reg v_2859) (concat (expression.bv_nat 16 0) (concat (extract v_12309 0 16) (concat (expression.bv_nat 16 0) (concat (extract v_12309 16 32) (concat (expression.bv_nat 16 0) (concat (extract v_12309 32 48) (concat (expression.bv_nat 16 0) (extract v_12309 48 64))))))));
      pure ()
    pat_end;
    pattern fun (v_2867 : Mem) (v_2868 : reg (bv 256)) => do
      v_12322 <- evaluateAddress v_2867;
      v_12323 <- load v_12322 16;
      setRegister (lhs.of_reg v_2868) (concat (expression.bv_nat 16 0) (concat (extract v_12323 0 16) (concat (expression.bv_nat 16 0) (concat (extract v_12323 16 32) (concat (expression.bv_nat 16 0) (concat (extract v_12323 32 48) (concat (expression.bv_nat 16 0) (concat (extract v_12323 48 64) (concat (expression.bv_nat 16 0) (concat (extract v_12323 64 80) (concat (expression.bv_nat 16 0) (concat (extract v_12323 80 96) (concat (expression.bv_nat 16 0) (concat (extract v_12323 96 112) (concat (expression.bv_nat 16 0) (extract v_12323 112 128))))))))))))))));
      pure ()
    pat_end
