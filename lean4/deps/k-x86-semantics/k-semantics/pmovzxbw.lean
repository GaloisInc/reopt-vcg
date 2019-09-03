def pmovzxbw1 : instruction :=
  definst "pmovzxbw" $ do
    pattern fun (v_2752 : reg (bv 128)) (v_2753 : reg (bv 128)) => do
      v_5525 <- getRegister v_2752;
      setRegister (lhs.of_reg v_2753) (concat (expression.bv_nat 8 0) (concat (extract v_5525 64 72) (concat (expression.bv_nat 8 0) (concat (extract v_5525 72 80) (concat (expression.bv_nat 8 0) (concat (extract v_5525 80 88) (concat (expression.bv_nat 8 0) (concat (extract v_5525 88 96) (concat (expression.bv_nat 8 0) (concat (extract v_5525 96 104) (concat (expression.bv_nat 8 0) (concat (extract v_5525 104 112) (concat (expression.bv_nat 8 0) (concat (extract v_5525 112 120) (concat (expression.bv_nat 8 0) (extract v_5525 120 128))))))))))))))));
      pure ()
    pat_end;
    pattern fun (v_2748 : Mem) (v_2749 : reg (bv 128)) => do
      v_12474 <- evaluateAddress v_2748;
      v_12475 <- load v_12474 8;
      setRegister (lhs.of_reg v_2749) (concat (expression.bv_nat 8 0) (concat (extract v_12475 0 8) (concat (expression.bv_nat 8 0) (concat (extract v_12475 8 16) (concat (expression.bv_nat 8 0) (concat (extract v_12475 16 24) (concat (expression.bv_nat 8 0) (concat (extract v_12475 24 32) (concat (expression.bv_nat 8 0) (concat (extract v_12475 32 40) (concat (expression.bv_nat 8 0) (concat (extract v_12475 40 48) (concat (expression.bv_nat 8 0) (concat (extract v_12475 48 56) (concat (expression.bv_nat 8 0) (extract v_12475 56 64))))))))))))))));
      pure ()
    pat_end
