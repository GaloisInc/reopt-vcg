def paddb1 : instruction :=
  definst "paddb" $ do
    pattern fun (v_3174 : reg (bv 128)) (v_3175 : reg (bv 128)) => do
      v_5618 <- getRegister v_3175;
      v_5620 <- getRegister v_3174;
      setRegister (lhs.of_reg v_3175) (concat (add (extract v_5618 0 8) (extract v_5620 0 8)) (concat (add (extract v_5618 8 16) (extract v_5620 8 16)) (concat (add (extract v_5618 16 24) (extract v_5620 16 24)) (concat (add (extract v_5618 24 32) (extract v_5620 24 32)) (concat (add (extract v_5618 32 40) (extract v_5620 32 40)) (concat (add (extract v_5618 40 48) (extract v_5620 40 48)) (concat (add (extract v_5618 48 56) (extract v_5620 48 56)) (concat (add (extract v_5618 56 64) (extract v_5620 56 64)) (concat (add (extract v_5618 64 72) (extract v_5620 64 72)) (concat (add (extract v_5618 72 80) (extract v_5620 72 80)) (concat (add (extract v_5618 80 88) (extract v_5620 80 88)) (concat (add (extract v_5618 88 96) (extract v_5620 88 96)) (concat (add (extract v_5618 96 104) (extract v_5620 96 104)) (concat (add (extract v_5618 104 112) (extract v_5620 104 112)) (concat (add (extract v_5618 112 120) (extract v_5620 112 120)) (add (extract v_5618 120 128) (extract v_5620 120 128)))))))))))))))));
      pure ()
    pat_end;
    pattern fun (v_3169 : Mem) (v_3170 : reg (bv 128)) => do
      v_9553 <- getRegister v_3170;
      v_9555 <- evaluateAddress v_3169;
      v_9556 <- load v_9555 16;
      setRegister (lhs.of_reg v_3170) (concat (add (extract v_9553 0 8) (extract v_9556 0 8)) (concat (add (extract v_9553 8 16) (extract v_9556 8 16)) (concat (add (extract v_9553 16 24) (extract v_9556 16 24)) (concat (add (extract v_9553 24 32) (extract v_9556 24 32)) (concat (add (extract v_9553 32 40) (extract v_9556 32 40)) (concat (add (extract v_9553 40 48) (extract v_9556 40 48)) (concat (add (extract v_9553 48 56) (extract v_9556 48 56)) (concat (add (extract v_9553 56 64) (extract v_9556 56 64)) (concat (add (extract v_9553 64 72) (extract v_9556 64 72)) (concat (add (extract v_9553 72 80) (extract v_9556 72 80)) (concat (add (extract v_9553 80 88) (extract v_9556 80 88)) (concat (add (extract v_9553 88 96) (extract v_9556 88 96)) (concat (add (extract v_9553 96 104) (extract v_9556 96 104)) (concat (add (extract v_9553 104 112) (extract v_9556 104 112)) (concat (add (extract v_9553 112 120) (extract v_9556 112 120)) (add (extract v_9553 120 128) (extract v_9556 120 128)))))))))))))))));
      pure ()
    pat_end
