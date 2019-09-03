def vpmovzxbq1 : instruction :=
  definst "vpmovzxbq" $ do
    pattern fun (v_2717 : reg (bv 128)) (v_2718 : reg (bv 128)) => do
      v_5774 <- getRegister v_2717;
      setRegister (lhs.of_reg v_2718) (concat (expression.bv_nat 56 0) (concat (extract v_5774 112 120) (concat (expression.bv_nat 56 0) (extract v_5774 120 128))));
      pure ()
    pat_end;
    pattern fun (v_2726 : reg (bv 128)) (v_2727 : reg (bv 256)) => do
      v_5785 <- getRegister v_2726;
      setRegister (lhs.of_reg v_2727) (concat (expression.bv_nat 56 0) (concat (extract v_5785 96 104) (concat (expression.bv_nat 56 0) (concat (extract v_5785 104 112) (concat (expression.bv_nat 56 0) (concat (extract v_5785 112 120) (concat (expression.bv_nat 56 0) (extract v_5785 120 128))))))));
      pure ()
    pat_end;
    pattern fun (v_2714 : Mem) (v_2713 : reg (bv 128)) => do
      v_12910 <- evaluateAddress v_2714;
      v_12911 <- load v_12910 2;
      setRegister (lhs.of_reg v_2713) (concat (expression.bv_nat 56 0) (concat (extract v_12911 0 8) (concat (expression.bv_nat 56 0) (extract v_12911 8 16))));
      pure ()
    pat_end;
    pattern fun (v_2722 : Mem) (v_2723 : reg (bv 256)) => do
      v_12918 <- evaluateAddress v_2722;
      v_12919 <- load v_12918 4;
      setRegister (lhs.of_reg v_2723) (concat (expression.bv_nat 56 0) (concat (extract v_12919 0 8) (concat (expression.bv_nat 56 0) (concat (extract v_12919 8 16) (concat (expression.bv_nat 56 0) (concat (extract v_12919 16 24) (concat (expression.bv_nat 56 0) (extract v_12919 24 32))))))));
      pure ()
    pat_end
