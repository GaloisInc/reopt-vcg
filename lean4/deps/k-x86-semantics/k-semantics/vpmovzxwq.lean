def vpmovzxwq1 : instruction :=
  definst "vpmovzxwq" $ do
    pattern fun (v_2801 : reg (bv 128)) (v_2802 : reg (bv 128)) => do
      v_5905 <- getRegister v_2801;
      setRegister (lhs.of_reg v_2802) (concat (expression.bv_nat 48 0) (concat (extract v_5905 96 112) (concat (expression.bv_nat 48 0) (extract v_5905 112 128))));
      pure ()
    pat_end;
    pattern fun (v_2810 : reg (bv 128)) (v_2812 : reg (bv 256)) => do
      v_5916 <- getRegister v_2810;
      setRegister (lhs.of_reg v_2812) (concat (expression.bv_nat 48 0) (concat (extract v_5916 64 80) (concat (expression.bv_nat 48 0) (concat (extract v_5916 80 96) (concat (expression.bv_nat 48 0) (concat (extract v_5916 96 112) (concat (expression.bv_nat 48 0) (extract v_5916 112 128))))))));
      pure ()
    pat_end;
    pattern fun (v_2796 : Mem) (v_2797 : reg (bv 128)) => do
      v_12526 <- evaluateAddress v_2796;
      v_12527 <- load v_12526 4;
      setRegister (lhs.of_reg v_2797) (concat (expression.bv_nat 48 0) (concat (extract v_12527 0 16) (concat (expression.bv_nat 48 0) (extract v_12527 16 32))));
      pure ()
    pat_end;
    pattern fun (v_2805 : Mem) (v_2807 : reg (bv 256)) => do
      v_12534 <- evaluateAddress v_2805;
      v_12535 <- load v_12534 8;
      setRegister (lhs.of_reg v_2807) (concat (expression.bv_nat 48 0) (concat (extract v_12535 0 16) (concat (expression.bv_nat 48 0) (concat (extract v_12535 16 32) (concat (expression.bv_nat 48 0) (concat (extract v_12535 32 48) (concat (expression.bv_nat 48 0) (extract v_12535 48 64))))))));
      pure ()
    pat_end
