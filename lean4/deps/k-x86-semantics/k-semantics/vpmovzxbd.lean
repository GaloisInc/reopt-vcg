def vpmovzxbd1 : instruction :=
  definst "vpmovzxbd" $ do
    pattern fun (v_2791 : reg (bv 128)) (v_2792 : reg (bv 128)) => do
      v_5753 <- getRegister v_2791;
      setRegister (lhs.of_reg v_2792) (concat (expression.bv_nat 24 0) (concat (extract v_5753 96 104) (concat (expression.bv_nat 24 0) (concat (extract v_5753 104 112) (concat (expression.bv_nat 24 0) (concat (extract v_5753 112 120) (concat (expression.bv_nat 24 0) (extract v_5753 120 128))))))));
      pure ()
    pat_end;
    pattern fun (v_2801 : reg (bv 128)) (v_2800 : reg (bv 256)) => do
      v_5770 <- getRegister v_2801;
      setRegister (lhs.of_reg v_2800) (concat (expression.bv_nat 24 0) (concat (extract v_5770 64 72) (concat (expression.bv_nat 24 0) (concat (extract v_5770 72 80) (concat (expression.bv_nat 24 0) (concat (extract v_5770 80 88) (concat (expression.bv_nat 24 0) (concat (extract v_5770 88 96) (concat (expression.bv_nat 24 0) (concat (extract v_5770 96 104) (concat (expression.bv_nat 24 0) (concat (extract v_5770 104 112) (concat (expression.bv_nat 24 0) (concat (extract v_5770 112 120) (concat (expression.bv_nat 24 0) (extract v_5770 120 128))))))))))))))));
      pure ()
    pat_end;
    pattern fun (v_2786 : Mem) (v_2787 : reg (bv 128)) => do
      v_12148 <- evaluateAddress v_2786;
      v_12149 <- load v_12148 4;
      setRegister (lhs.of_reg v_2787) (concat (expression.bv_nat 24 0) (concat (extract v_12149 0 8) (concat (expression.bv_nat 24 0) (concat (extract v_12149 8 16) (concat (expression.bv_nat 24 0) (concat (extract v_12149 16 24) (concat (expression.bv_nat 24 0) (extract v_12149 24 32))))))));
      pure ()
    pat_end;
    pattern fun (v_2795 : Mem) (v_2796 : reg (bv 256)) => do
      v_12162 <- evaluateAddress v_2795;
      v_12163 <- load v_12162 8;
      setRegister (lhs.of_reg v_2796) (concat (expression.bv_nat 24 0) (concat (extract v_12163 0 8) (concat (expression.bv_nat 24 0) (concat (extract v_12163 8 16) (concat (expression.bv_nat 24 0) (concat (extract v_12163 16 24) (concat (expression.bv_nat 24 0) (concat (extract v_12163 24 32) (concat (expression.bv_nat 24 0) (concat (extract v_12163 32 40) (concat (expression.bv_nat 24 0) (concat (extract v_12163 40 48) (concat (expression.bv_nat 24 0) (concat (extract v_12163 48 56) (concat (expression.bv_nat 24 0) (extract v_12163 56 64))))))))))))))));
      pure ()
    pat_end
