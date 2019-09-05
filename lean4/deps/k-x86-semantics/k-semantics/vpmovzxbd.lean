def vpmovzxbd1 : instruction :=
  definst "vpmovzxbd" $ do
    pattern fun (v_2764 : reg (bv 128)) (v_2765 : reg (bv 128)) => do
      v_5726 <- getRegister v_2764;
      setRegister (lhs.of_reg v_2765) (concat (expression.bv_nat 24 0) (concat (extract v_5726 96 104) (concat (expression.bv_nat 24 0) (concat (extract v_5726 104 112) (concat (expression.bv_nat 24 0) (concat (extract v_5726 112 120) (concat (expression.bv_nat 24 0) (extract v_5726 120 128))))))));
      pure ()
    pat_end;
    pattern fun (v_2774 : reg (bv 128)) (v_2773 : reg (bv 256)) => do
      v_5743 <- getRegister v_2774;
      setRegister (lhs.of_reg v_2773) (concat (expression.bv_nat 24 0) (concat (extract v_5743 64 72) (concat (expression.bv_nat 24 0) (concat (extract v_5743 72 80) (concat (expression.bv_nat 24 0) (concat (extract v_5743 80 88) (concat (expression.bv_nat 24 0) (concat (extract v_5743 88 96) (concat (expression.bv_nat 24 0) (concat (extract v_5743 96 104) (concat (expression.bv_nat 24 0) (concat (extract v_5743 104 112) (concat (expression.bv_nat 24 0) (concat (extract v_5743 112 120) (concat (expression.bv_nat 24 0) (extract v_5743 120 128))))))))))))))));
      pure ()
    pat_end;
    pattern fun (v_2759 : Mem) (v_2760 : reg (bv 128)) => do
      v_12121 <- evaluateAddress v_2759;
      v_12122 <- load v_12121 4;
      setRegister (lhs.of_reg v_2760) (concat (expression.bv_nat 24 0) (concat (extract v_12122 0 8) (concat (expression.bv_nat 24 0) (concat (extract v_12122 8 16) (concat (expression.bv_nat 24 0) (concat (extract v_12122 16 24) (concat (expression.bv_nat 24 0) (extract v_12122 24 32))))))));
      pure ()
    pat_end;
    pattern fun (v_2768 : Mem) (v_2769 : reg (bv 256)) => do
      v_12135 <- evaluateAddress v_2768;
      v_12136 <- load v_12135 8;
      setRegister (lhs.of_reg v_2769) (concat (expression.bv_nat 24 0) (concat (extract v_12136 0 8) (concat (expression.bv_nat 24 0) (concat (extract v_12136 8 16) (concat (expression.bv_nat 24 0) (concat (extract v_12136 16 24) (concat (expression.bv_nat 24 0) (concat (extract v_12136 24 32) (concat (expression.bv_nat 24 0) (concat (extract v_12136 32 40) (concat (expression.bv_nat 24 0) (concat (extract v_12136 40 48) (concat (expression.bv_nat 24 0) (concat (extract v_12136 48 56) (concat (expression.bv_nat 24 0) (extract v_12136 56 64))))))))))))))));
      pure ()
    pat_end
