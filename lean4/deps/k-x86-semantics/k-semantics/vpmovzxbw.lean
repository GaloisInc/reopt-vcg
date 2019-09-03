def vpmovzxbw1 : instruction :=
  definst "vpmovzxbw" $ do
    pattern fun (v_2747 : reg (bv 128)) (v_2748 : reg (bv 128)) => do
      v_5749 <- getRegister v_2747;
      setRegister (lhs.of_reg v_2748) (concat (expression.bv_nat 8 0) (concat (extract v_5749 64 72) (concat (expression.bv_nat 8 0) (concat (extract v_5749 72 80) (concat (expression.bv_nat 8 0) (concat (extract v_5749 80 88) (concat (expression.bv_nat 8 0) (concat (extract v_5749 88 96) (concat (expression.bv_nat 8 0) (concat (extract v_5749 96 104) (concat (expression.bv_nat 8 0) (concat (extract v_5749 104 112) (concat (expression.bv_nat 8 0) (concat (extract v_5749 112 120) (concat (expression.bv_nat 8 0) (extract v_5749 120 128))))))))))))))));
      pure ()
    pat_end;
    pattern fun (v_2756 : reg (bv 128)) (v_2758 : reg (bv 256)) => do
      v_5778 <- getRegister v_2756;
      setRegister (lhs.of_reg v_2758) (concat (expression.bv_nat 8 0) (concat (extract v_5778 0 8) (concat (expression.bv_nat 8 0) (concat (extract v_5778 8 16) (concat (expression.bv_nat 8 0) (concat (extract v_5778 16 24) (concat (expression.bv_nat 8 0) (concat (extract v_5778 24 32) (concat (expression.bv_nat 8 0) (concat (extract v_5778 32 40) (concat (expression.bv_nat 8 0) (concat (extract v_5778 40 48) (concat (expression.bv_nat 8 0) (concat (extract v_5778 48 56) (concat (expression.bv_nat 8 0) (concat (extract v_5778 56 64) (concat (expression.bv_nat 8 0) (concat (extract v_5778 64 72) (concat (expression.bv_nat 8 0) (concat (extract v_5778 72 80) (concat (expression.bv_nat 8 0) (concat (extract v_5778 80 88) (concat (expression.bv_nat 8 0) (concat (extract v_5778 88 96) (concat (expression.bv_nat 8 0) (concat (extract v_5778 96 104) (concat (expression.bv_nat 8 0) (concat (extract v_5778 104 112) (concat (expression.bv_nat 8 0) (concat (extract v_5778 112 120) (concat (expression.bv_nat 8 0) (extract v_5778 120 128))))))))))))))))))))))))))))))));
      pure ()
    pat_end;
    pattern fun (v_2742 : Mem) (v_2743 : reg (bv 128)) => do
      v_12388 <- evaluateAddress v_2742;
      v_12389 <- load v_12388 8;
      setRegister (lhs.of_reg v_2743) (concat (expression.bv_nat 8 0) (concat (extract v_12389 0 8) (concat (expression.bv_nat 8 0) (concat (extract v_12389 8 16) (concat (expression.bv_nat 8 0) (concat (extract v_12389 16 24) (concat (expression.bv_nat 8 0) (concat (extract v_12389 24 32) (concat (expression.bv_nat 8 0) (concat (extract v_12389 32 40) (concat (expression.bv_nat 8 0) (concat (extract v_12389 40 48) (concat (expression.bv_nat 8 0) (concat (extract v_12389 48 56) (concat (expression.bv_nat 8 0) (extract v_12389 56 64))))))))))))))));
      pure ()
    pat_end;
    pattern fun (v_2751 : Mem) (v_2753 : reg (bv 256)) => do
      v_12414 <- evaluateAddress v_2751;
      v_12415 <- load v_12414 16;
      setRegister (lhs.of_reg v_2753) (concat (expression.bv_nat 8 0) (concat (extract v_12415 0 8) (concat (expression.bv_nat 8 0) (concat (extract v_12415 8 16) (concat (expression.bv_nat 8 0) (concat (extract v_12415 16 24) (concat (expression.bv_nat 8 0) (concat (extract v_12415 24 32) (concat (expression.bv_nat 8 0) (concat (extract v_12415 32 40) (concat (expression.bv_nat 8 0) (concat (extract v_12415 40 48) (concat (expression.bv_nat 8 0) (concat (extract v_12415 48 56) (concat (expression.bv_nat 8 0) (concat (extract v_12415 56 64) (concat (expression.bv_nat 8 0) (concat (extract v_12415 64 72) (concat (expression.bv_nat 8 0) (concat (extract v_12415 72 80) (concat (expression.bv_nat 8 0) (concat (extract v_12415 80 88) (concat (expression.bv_nat 8 0) (concat (extract v_12415 88 96) (concat (expression.bv_nat 8 0) (concat (extract v_12415 96 104) (concat (expression.bv_nat 8 0) (concat (extract v_12415 104 112) (concat (expression.bv_nat 8 0) (concat (extract v_12415 112 120) (concat (expression.bv_nat 8 0) (extract v_12415 120 128))))))))))))))))))))))))))))))));
      pure ()
    pat_end
