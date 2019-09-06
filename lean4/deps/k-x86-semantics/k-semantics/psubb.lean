def psubb1 : instruction :=
  definst "psubb" $ do
    pattern fun (v_3172 : reg (bv 128)) (v_3173 : reg (bv 128)) => do
      v_7973 <- getRegister v_3173;
      v_7975 <- getRegister v_3172;
      setRegister (lhs.of_reg v_3173) (concat (sub (extract v_7973 0 8) (extract v_7975 0 8)) (concat (sub (extract v_7973 8 16) (extract v_7975 8 16)) (concat (sub (extract v_7973 16 24) (extract v_7975 16 24)) (concat (sub (extract v_7973 24 32) (extract v_7975 24 32)) (concat (sub (extract v_7973 32 40) (extract v_7975 32 40)) (concat (sub (extract v_7973 40 48) (extract v_7975 40 48)) (concat (sub (extract v_7973 48 56) (extract v_7975 48 56)) (concat (sub (extract v_7973 56 64) (extract v_7975 56 64)) (concat (sub (extract v_7973 64 72) (extract v_7975 64 72)) (concat (sub (extract v_7973 72 80) (extract v_7975 72 80)) (concat (sub (extract v_7973 80 88) (extract v_7975 80 88)) (concat (sub (extract v_7973 88 96) (extract v_7975 88 96)) (concat (sub (extract v_7973 96 104) (extract v_7975 96 104)) (concat (sub (extract v_7973 104 112) (extract v_7975 104 112)) (concat (sub (extract v_7973 112 120) (extract v_7975 112 120)) (sub (extract v_7973 120 128) (extract v_7975 120 128)))))))))))))))));
      pure ()
    pat_end;
    pattern fun (v_3168 : Mem) (v_3169 : reg (bv 128)) => do
      v_14403 <- getRegister v_3169;
      v_14405 <- evaluateAddress v_3168;
      v_14406 <- load v_14405 16;
      setRegister (lhs.of_reg v_3169) (concat (sub (extract v_14403 0 8) (extract v_14406 0 8)) (concat (sub (extract v_14403 8 16) (extract v_14406 8 16)) (concat (sub (extract v_14403 16 24) (extract v_14406 16 24)) (concat (sub (extract v_14403 24 32) (extract v_14406 24 32)) (concat (sub (extract v_14403 32 40) (extract v_14406 32 40)) (concat (sub (extract v_14403 40 48) (extract v_14406 40 48)) (concat (sub (extract v_14403 48 56) (extract v_14406 48 56)) (concat (sub (extract v_14403 56 64) (extract v_14406 56 64)) (concat (sub (extract v_14403 64 72) (extract v_14406 64 72)) (concat (sub (extract v_14403 72 80) (extract v_14406 72 80)) (concat (sub (extract v_14403 80 88) (extract v_14406 80 88)) (concat (sub (extract v_14403 88 96) (extract v_14406 88 96)) (concat (sub (extract v_14403 96 104) (extract v_14406 96 104)) (concat (sub (extract v_14403 104 112) (extract v_14406 104 112)) (concat (sub (extract v_14403 112 120) (extract v_14406 112 120)) (sub (extract v_14403 120 128) (extract v_14406 120 128)))))))))))))))));
      pure ()
    pat_end
