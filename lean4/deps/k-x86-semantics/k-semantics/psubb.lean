def psubb1 : instruction :=
  definst "psubb" $ do
    pattern fun (v_3095 : reg (bv 128)) (v_3096 : reg (bv 128)) => do
      v_8011 <- getRegister v_3096;
      v_8013 <- getRegister v_3095;
      setRegister (lhs.of_reg v_3096) (concat (sub (extract v_8011 0 8) (extract v_8013 0 8)) (concat (sub (extract v_8011 8 16) (extract v_8013 8 16)) (concat (sub (extract v_8011 16 24) (extract v_8013 16 24)) (concat (sub (extract v_8011 24 32) (extract v_8013 24 32)) (concat (sub (extract v_8011 32 40) (extract v_8013 32 40)) (concat (sub (extract v_8011 40 48) (extract v_8013 40 48)) (concat (sub (extract v_8011 48 56) (extract v_8013 48 56)) (concat (sub (extract v_8011 56 64) (extract v_8013 56 64)) (concat (sub (extract v_8011 64 72) (extract v_8013 64 72)) (concat (sub (extract v_8011 72 80) (extract v_8013 72 80)) (concat (sub (extract v_8011 80 88) (extract v_8013 80 88)) (concat (sub (extract v_8011 88 96) (extract v_8013 88 96)) (concat (sub (extract v_8011 96 104) (extract v_8013 96 104)) (concat (sub (extract v_8011 104 112) (extract v_8013 104 112)) (concat (sub (extract v_8011 112 120) (extract v_8013 112 120)) (sub (extract v_8011 120 128) (extract v_8013 120 128)))))))))))))))));
      pure ()
    pat_end;
    pattern fun (v_3091 : Mem) (v_3092 : reg (bv 128)) => do
      v_14629 <- getRegister v_3092;
      v_14631 <- evaluateAddress v_3091;
      v_14632 <- load v_14631 16;
      setRegister (lhs.of_reg v_3092) (concat (sub (extract v_14629 0 8) (extract v_14632 0 8)) (concat (sub (extract v_14629 8 16) (extract v_14632 8 16)) (concat (sub (extract v_14629 16 24) (extract v_14632 16 24)) (concat (sub (extract v_14629 24 32) (extract v_14632 24 32)) (concat (sub (extract v_14629 32 40) (extract v_14632 32 40)) (concat (sub (extract v_14629 40 48) (extract v_14632 40 48)) (concat (sub (extract v_14629 48 56) (extract v_14632 48 56)) (concat (sub (extract v_14629 56 64) (extract v_14632 56 64)) (concat (sub (extract v_14629 64 72) (extract v_14632 64 72)) (concat (sub (extract v_14629 72 80) (extract v_14632 72 80)) (concat (sub (extract v_14629 80 88) (extract v_14632 80 88)) (concat (sub (extract v_14629 88 96) (extract v_14632 88 96)) (concat (sub (extract v_14629 96 104) (extract v_14632 96 104)) (concat (sub (extract v_14629 104 112) (extract v_14632 104 112)) (concat (sub (extract v_14629 112 120) (extract v_14632 112 120)) (sub (extract v_14629 120 128) (extract v_14632 120 128)))))))))))))))));
      pure ()
    pat_end
