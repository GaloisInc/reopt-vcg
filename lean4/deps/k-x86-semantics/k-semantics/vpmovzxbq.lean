def vpmovzxbq1 : instruction :=
  definst "vpmovzxbq" $ do
    pattern fun (v_2809 : reg (bv 128)) (v_2810 : reg (bv 128)) => do
      v_5799 <- getRegister v_2809;
      setRegister (lhs.of_reg v_2810) (concat (expression.bv_nat 56 0) (concat (extract v_5799 112 120) (concat (expression.bv_nat 56 0) (extract v_5799 120 128))));
      pure ()
    pat_end;
    pattern fun (v_2819 : reg (bv 128)) (v_2818 : reg (bv 256)) => do
      v_5810 <- getRegister v_2819;
      setRegister (lhs.of_reg v_2818) (concat (expression.bv_nat 56 0) (concat (extract v_5810 96 104) (concat (expression.bv_nat 56 0) (concat (extract v_5810 104 112) (concat (expression.bv_nat 56 0) (concat (extract v_5810 112 120) (concat (expression.bv_nat 56 0) (extract v_5810 120 128))))))));
      pure ()
    pat_end;
    pattern fun (v_2804 : Mem) (v_2805 : reg (bv 128)) => do
      v_12188 <- evaluateAddress v_2804;
      v_12189 <- load v_12188 2;
      setRegister (lhs.of_reg v_2805) (concat (expression.bv_nat 56 0) (concat (extract v_12189 0 8) (concat (expression.bv_nat 56 0) (extract v_12189 8 16))));
      pure ()
    pat_end;
    pattern fun (v_2813 : Mem) (v_2814 : reg (bv 256)) => do
      v_12196 <- evaluateAddress v_2813;
      v_12197 <- load v_12196 4;
      setRegister (lhs.of_reg v_2814) (concat (expression.bv_nat 56 0) (concat (extract v_12197 0 8) (concat (expression.bv_nat 56 0) (concat (extract v_12197 8 16) (concat (expression.bv_nat 56 0) (concat (extract v_12197 16 24) (concat (expression.bv_nat 56 0) (extract v_12197 24 32))))))));
      pure ()
    pat_end
