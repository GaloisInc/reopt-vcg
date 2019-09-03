def psubb1 : instruction :=
  definst "psubb" $ do
    pattern fun (v_3081 : reg (bv 128)) (v_3082 : reg (bv 128)) => do
      v_8281 <- getRegister v_3082;
      v_8283 <- getRegister v_3081;
      setRegister (lhs.of_reg v_3082) (concat (sub (extract v_8281 0 8) (extract v_8283 0 8)) (concat (sub (extract v_8281 8 16) (extract v_8283 8 16)) (concat (sub (extract v_8281 16 24) (extract v_8283 16 24)) (concat (sub (extract v_8281 24 32) (extract v_8283 24 32)) (concat (sub (extract v_8281 32 40) (extract v_8283 32 40)) (concat (sub (extract v_8281 40 48) (extract v_8283 40 48)) (concat (sub (extract v_8281 48 56) (extract v_8283 48 56)) (concat (sub (extract v_8281 56 64) (extract v_8283 56 64)) (concat (sub (extract v_8281 64 72) (extract v_8283 64 72)) (concat (sub (extract v_8281 72 80) (extract v_8283 72 80)) (concat (sub (extract v_8281 80 88) (extract v_8283 80 88)) (concat (sub (extract v_8281 88 96) (extract v_8283 88 96)) (concat (sub (extract v_8281 96 104) (extract v_8283 96 104)) (concat (sub (extract v_8281 104 112) (extract v_8283 104 112)) (concat (sub (extract v_8281 112 120) (extract v_8283 112 120)) (sub (extract v_8281 120 128) (extract v_8283 120 128)))))))))))))))));
      pure ()
    pat_end;
    pattern fun (v_3076 : Mem) (v_3077 : reg (bv 128)) => do
      v_15198 <- getRegister v_3077;
      v_15200 <- evaluateAddress v_3076;
      v_15201 <- load v_15200 16;
      setRegister (lhs.of_reg v_3077) (concat (sub (extract v_15198 0 8) (extract v_15201 0 8)) (concat (sub (extract v_15198 8 16) (extract v_15201 8 16)) (concat (sub (extract v_15198 16 24) (extract v_15201 16 24)) (concat (sub (extract v_15198 24 32) (extract v_15201 24 32)) (concat (sub (extract v_15198 32 40) (extract v_15201 32 40)) (concat (sub (extract v_15198 40 48) (extract v_15201 40 48)) (concat (sub (extract v_15198 48 56) (extract v_15201 48 56)) (concat (sub (extract v_15198 56 64) (extract v_15201 56 64)) (concat (sub (extract v_15198 64 72) (extract v_15201 64 72)) (concat (sub (extract v_15198 72 80) (extract v_15201 72 80)) (concat (sub (extract v_15198 80 88) (extract v_15201 80 88)) (concat (sub (extract v_15198 88 96) (extract v_15201 88 96)) (concat (sub (extract v_15198 96 104) (extract v_15201 96 104)) (concat (sub (extract v_15198 104 112) (extract v_15201 104 112)) (concat (sub (extract v_15198 112 120) (extract v_15201 112 120)) (sub (extract v_15198 120 128) (extract v_15201 120 128)))))))))))))))));
      pure ()
    pat_end
