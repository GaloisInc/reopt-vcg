def vpmovzxbq1 : instruction :=
  definst "vpmovzxbq" $ do
    pattern fun (v_2782 : reg (bv 128)) (v_2783 : reg (bv 128)) => do
      v_5772 <- getRegister v_2782;
      setRegister (lhs.of_reg v_2783) (concat (expression.bv_nat 56 0) (concat (extract v_5772 112 120) (concat (expression.bv_nat 56 0) (extract v_5772 120 128))));
      pure ()
    pat_end;
    pattern fun (v_2792 : reg (bv 128)) (v_2791 : reg (bv 256)) => do
      v_5783 <- getRegister v_2792;
      setRegister (lhs.of_reg v_2791) (concat (expression.bv_nat 56 0) (concat (extract v_5783 96 104) (concat (expression.bv_nat 56 0) (concat (extract v_5783 104 112) (concat (expression.bv_nat 56 0) (concat (extract v_5783 112 120) (concat (expression.bv_nat 56 0) (extract v_5783 120 128))))))));
      pure ()
    pat_end;
    pattern fun (v_2777 : Mem) (v_2778 : reg (bv 128)) => do
      v_12161 <- evaluateAddress v_2777;
      v_12162 <- load v_12161 2;
      setRegister (lhs.of_reg v_2778) (concat (expression.bv_nat 56 0) (concat (extract v_12162 0 8) (concat (expression.bv_nat 56 0) (extract v_12162 8 16))));
      pure ()
    pat_end;
    pattern fun (v_2786 : Mem) (v_2787 : reg (bv 256)) => do
      v_12169 <- evaluateAddress v_2786;
      v_12170 <- load v_12169 4;
      setRegister (lhs.of_reg v_2787) (concat (expression.bv_nat 56 0) (concat (extract v_12170 0 8) (concat (expression.bv_nat 56 0) (concat (extract v_12170 8 16) (concat (expression.bv_nat 56 0) (concat (extract v_12170 16 24) (concat (expression.bv_nat 56 0) (extract v_12170 24 32))))))));
      pure ()
    pat_end
