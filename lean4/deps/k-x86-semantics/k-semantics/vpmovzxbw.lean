def vpmovzxbw1 : instruction :=
  definst "vpmovzxbw" $ do
    pattern fun (v_2735 : reg (bv 128)) (v_2736 : reg (bv 128)) => do
      v_5802 <- getRegister v_2735;
      setRegister (lhs.of_reg v_2736) (concat (expression.bv_nat 8 0) (concat (extract v_5802 64 72) (concat (expression.bv_nat 8 0) (concat (extract v_5802 72 80) (concat (expression.bv_nat 8 0) (concat (extract v_5802 80 88) (concat (expression.bv_nat 8 0) (concat (extract v_5802 88 96) (concat (expression.bv_nat 8 0) (concat (extract v_5802 96 104) (concat (expression.bv_nat 8 0) (concat (extract v_5802 104 112) (concat (expression.bv_nat 8 0) (concat (extract v_5802 112 120) (concat (expression.bv_nat 8 0) (extract v_5802 120 128))))))))))))))));
      pure ()
    pat_end;
    pattern fun (v_2744 : reg (bv 128)) (v_2745 : reg (bv 256)) => do
      v_5831 <- getRegister v_2744;
      setRegister (lhs.of_reg v_2745) (concat (expression.bv_nat 8 0) (concat (extract v_5831 0 8) (concat (expression.bv_nat 8 0) (concat (extract v_5831 8 16) (concat (expression.bv_nat 8 0) (concat (extract v_5831 16 24) (concat (expression.bv_nat 8 0) (concat (extract v_5831 24 32) (concat (expression.bv_nat 8 0) (concat (extract v_5831 32 40) (concat (expression.bv_nat 8 0) (concat (extract v_5831 40 48) (concat (expression.bv_nat 8 0) (concat (extract v_5831 48 56) (concat (expression.bv_nat 8 0) (concat (extract v_5831 56 64) (concat (expression.bv_nat 8 0) (concat (extract v_5831 64 72) (concat (expression.bv_nat 8 0) (concat (extract v_5831 72 80) (concat (expression.bv_nat 8 0) (concat (extract v_5831 80 88) (concat (expression.bv_nat 8 0) (concat (extract v_5831 88 96) (concat (expression.bv_nat 8 0) (concat (extract v_5831 96 104) (concat (expression.bv_nat 8 0) (concat (extract v_5831 104 112) (concat (expression.bv_nat 8 0) (concat (extract v_5831 112 120) (concat (expression.bv_nat 8 0) (extract v_5831 120 128))))))))))))))))))))))))))))))));
      pure ()
    pat_end;
    pattern fun (v_2732 : Mem) (v_2731 : reg (bv 128)) => do
      v_12932 <- evaluateAddress v_2732;
      v_12933 <- load v_12932 8;
      setRegister (lhs.of_reg v_2731) (concat (expression.bv_nat 8 0) (concat (extract v_12933 0 8) (concat (expression.bv_nat 8 0) (concat (extract v_12933 8 16) (concat (expression.bv_nat 8 0) (concat (extract v_12933 16 24) (concat (expression.bv_nat 8 0) (concat (extract v_12933 24 32) (concat (expression.bv_nat 8 0) (concat (extract v_12933 32 40) (concat (expression.bv_nat 8 0) (concat (extract v_12933 40 48) (concat (expression.bv_nat 8 0) (concat (extract v_12933 48 56) (concat (expression.bv_nat 8 0) (extract v_12933 56 64))))))))))))))));
      pure ()
    pat_end;
    pattern fun (v_2740 : Mem) (v_2741 : reg (bv 256)) => do
      v_12958 <- evaluateAddress v_2740;
      v_12959 <- load v_12958 16;
      setRegister (lhs.of_reg v_2741) (concat (expression.bv_nat 8 0) (concat (extract v_12959 0 8) (concat (expression.bv_nat 8 0) (concat (extract v_12959 8 16) (concat (expression.bv_nat 8 0) (concat (extract v_12959 16 24) (concat (expression.bv_nat 8 0) (concat (extract v_12959 24 32) (concat (expression.bv_nat 8 0) (concat (extract v_12959 32 40) (concat (expression.bv_nat 8 0) (concat (extract v_12959 40 48) (concat (expression.bv_nat 8 0) (concat (extract v_12959 48 56) (concat (expression.bv_nat 8 0) (concat (extract v_12959 56 64) (concat (expression.bv_nat 8 0) (concat (extract v_12959 64 72) (concat (expression.bv_nat 8 0) (concat (extract v_12959 72 80) (concat (expression.bv_nat 8 0) (concat (extract v_12959 80 88) (concat (expression.bv_nat 8 0) (concat (extract v_12959 88 96) (concat (expression.bv_nat 8 0) (concat (extract v_12959 96 104) (concat (expression.bv_nat 8 0) (concat (extract v_12959 104 112) (concat (expression.bv_nat 8 0) (concat (extract v_12959 112 120) (concat (expression.bv_nat 8 0) (extract v_12959 120 128))))))))))))))))))))))))))))))));
      pure ()
    pat_end
