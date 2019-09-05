def psubb1 : instruction :=
  definst "psubb" $ do
    pattern fun (v_3144 : reg (bv 128)) (v_3145 : reg (bv 128)) => do
      v_7946 <- getRegister v_3145;
      v_7948 <- getRegister v_3144;
      setRegister (lhs.of_reg v_3145) (concat (sub (extract v_7946 0 8) (extract v_7948 0 8)) (concat (sub (extract v_7946 8 16) (extract v_7948 8 16)) (concat (sub (extract v_7946 16 24) (extract v_7948 16 24)) (concat (sub (extract v_7946 24 32) (extract v_7948 24 32)) (concat (sub (extract v_7946 32 40) (extract v_7948 32 40)) (concat (sub (extract v_7946 40 48) (extract v_7948 40 48)) (concat (sub (extract v_7946 48 56) (extract v_7948 48 56)) (concat (sub (extract v_7946 56 64) (extract v_7948 56 64)) (concat (sub (extract v_7946 64 72) (extract v_7948 64 72)) (concat (sub (extract v_7946 72 80) (extract v_7948 72 80)) (concat (sub (extract v_7946 80 88) (extract v_7948 80 88)) (concat (sub (extract v_7946 88 96) (extract v_7948 88 96)) (concat (sub (extract v_7946 96 104) (extract v_7948 96 104)) (concat (sub (extract v_7946 104 112) (extract v_7948 104 112)) (concat (sub (extract v_7946 112 120) (extract v_7948 112 120)) (sub (extract v_7946 120 128) (extract v_7948 120 128)))))))))))))))));
      pure ()
    pat_end;
    pattern fun (v_3141 : Mem) (v_3140 : reg (bv 128)) => do
      v_14427 <- getRegister v_3140;
      v_14429 <- evaluateAddress v_3141;
      v_14430 <- load v_14429 16;
      setRegister (lhs.of_reg v_3140) (concat (sub (extract v_14427 0 8) (extract v_14430 0 8)) (concat (sub (extract v_14427 8 16) (extract v_14430 8 16)) (concat (sub (extract v_14427 16 24) (extract v_14430 16 24)) (concat (sub (extract v_14427 24 32) (extract v_14430 24 32)) (concat (sub (extract v_14427 32 40) (extract v_14430 32 40)) (concat (sub (extract v_14427 40 48) (extract v_14430 40 48)) (concat (sub (extract v_14427 48 56) (extract v_14430 48 56)) (concat (sub (extract v_14427 56 64) (extract v_14430 56 64)) (concat (sub (extract v_14427 64 72) (extract v_14430 64 72)) (concat (sub (extract v_14427 72 80) (extract v_14430 72 80)) (concat (sub (extract v_14427 80 88) (extract v_14430 80 88)) (concat (sub (extract v_14427 88 96) (extract v_14430 88 96)) (concat (sub (extract v_14427 96 104) (extract v_14430 96 104)) (concat (sub (extract v_14427 104 112) (extract v_14430 104 112)) (concat (sub (extract v_14427 112 120) (extract v_14430 112 120)) (sub (extract v_14427 120 128) (extract v_14430 120 128)))))))))))))))));
      pure ()
    pat_end
