def vpmovzxbw1 : instruction :=
  definst "vpmovzxbw" $ do
    pattern fun (v_2800 : reg (bv 128)) (v_2801 : reg (bv 128)) => do
      v_5800 <- getRegister v_2800;
      setRegister (lhs.of_reg v_2801) (concat (expression.bv_nat 8 0) (concat (extract v_5800 64 72) (concat (expression.bv_nat 8 0) (concat (extract v_5800 72 80) (concat (expression.bv_nat 8 0) (concat (extract v_5800 80 88) (concat (expression.bv_nat 8 0) (concat (extract v_5800 88 96) (concat (expression.bv_nat 8 0) (concat (extract v_5800 96 104) (concat (expression.bv_nat 8 0) (concat (extract v_5800 104 112) (concat (expression.bv_nat 8 0) (concat (extract v_5800 112 120) (concat (expression.bv_nat 8 0) (extract v_5800 120 128))))))))))))))));
      pure ()
    pat_end;
    pattern fun (v_2810 : reg (bv 128)) (v_2809 : reg (bv 256)) => do
      v_5829 <- getRegister v_2810;
      setRegister (lhs.of_reg v_2809) (concat (expression.bv_nat 8 0) (concat (extract v_5829 0 8) (concat (expression.bv_nat 8 0) (concat (extract v_5829 8 16) (concat (expression.bv_nat 8 0) (concat (extract v_5829 16 24) (concat (expression.bv_nat 8 0) (concat (extract v_5829 24 32) (concat (expression.bv_nat 8 0) (concat (extract v_5829 32 40) (concat (expression.bv_nat 8 0) (concat (extract v_5829 40 48) (concat (expression.bv_nat 8 0) (concat (extract v_5829 48 56) (concat (expression.bv_nat 8 0) (concat (extract v_5829 56 64) (concat (expression.bv_nat 8 0) (concat (extract v_5829 64 72) (concat (expression.bv_nat 8 0) (concat (extract v_5829 72 80) (concat (expression.bv_nat 8 0) (concat (extract v_5829 80 88) (concat (expression.bv_nat 8 0) (concat (extract v_5829 88 96) (concat (expression.bv_nat 8 0) (concat (extract v_5829 96 104) (concat (expression.bv_nat 8 0) (concat (extract v_5829 104 112) (concat (expression.bv_nat 8 0) (concat (extract v_5829 112 120) (concat (expression.bv_nat 8 0) (extract v_5829 120 128))))))))))))))))))))))))))))))));
      pure ()
    pat_end;
    pattern fun (v_2795 : Mem) (v_2796 : reg (bv 128)) => do
      v_12183 <- evaluateAddress v_2795;
      v_12184 <- load v_12183 8;
      setRegister (lhs.of_reg v_2796) (concat (expression.bv_nat 8 0) (concat (extract v_12184 0 8) (concat (expression.bv_nat 8 0) (concat (extract v_12184 8 16) (concat (expression.bv_nat 8 0) (concat (extract v_12184 16 24) (concat (expression.bv_nat 8 0) (concat (extract v_12184 24 32) (concat (expression.bv_nat 8 0) (concat (extract v_12184 32 40) (concat (expression.bv_nat 8 0) (concat (extract v_12184 40 48) (concat (expression.bv_nat 8 0) (concat (extract v_12184 48 56) (concat (expression.bv_nat 8 0) (extract v_12184 56 64))))))))))))))));
      pure ()
    pat_end;
    pattern fun (v_2804 : Mem) (v_2805 : reg (bv 256)) => do
      v_12209 <- evaluateAddress v_2804;
      v_12210 <- load v_12209 16;
      setRegister (lhs.of_reg v_2805) (concat (expression.bv_nat 8 0) (concat (extract v_12210 0 8) (concat (expression.bv_nat 8 0) (concat (extract v_12210 8 16) (concat (expression.bv_nat 8 0) (concat (extract v_12210 16 24) (concat (expression.bv_nat 8 0) (concat (extract v_12210 24 32) (concat (expression.bv_nat 8 0) (concat (extract v_12210 32 40) (concat (expression.bv_nat 8 0) (concat (extract v_12210 40 48) (concat (expression.bv_nat 8 0) (concat (extract v_12210 48 56) (concat (expression.bv_nat 8 0) (concat (extract v_12210 56 64) (concat (expression.bv_nat 8 0) (concat (extract v_12210 64 72) (concat (expression.bv_nat 8 0) (concat (extract v_12210 72 80) (concat (expression.bv_nat 8 0) (concat (extract v_12210 80 88) (concat (expression.bv_nat 8 0) (concat (extract v_12210 88 96) (concat (expression.bv_nat 8 0) (concat (extract v_12210 96 104) (concat (expression.bv_nat 8 0) (concat (extract v_12210 104 112) (concat (expression.bv_nat 8 0) (concat (extract v_12210 112 120) (concat (expression.bv_nat 8 0) (extract v_12210 120 128))))))))))))))))))))))))))))))));
      pure ()
    pat_end
