def vpunpckhwd1 : instruction :=
  definst "vpunpckhwd" $ do
    pattern fun (v_2737 : reg (bv 128)) (v_2738 : reg (bv 128)) (v_2739 : reg (bv 128)) => do
      v_6270 <- getRegister v_2737;
      v_6272 <- getRegister v_2738;
      setRegister (lhs.of_reg v_2739) (concat (concat (extract v_6270 0 16) (extract v_6272 0 16)) (concat (concat (extract v_6270 16 32) (extract v_6272 16 32)) (concat (concat (extract v_6270 32 48) (extract v_6272 32 48)) (concat (extract v_6270 48 64) (extract v_6272 48 64)))));
      pure ()
    pat_end;
    pattern fun (v_2748 : reg (bv 256)) (v_2749 : reg (bv 256)) (v_2750 : reg (bv 256)) => do
      v_6293 <- getRegister v_2748;
      v_6295 <- getRegister v_2749;
      setRegister (lhs.of_reg v_2750) (concat (concat (extract v_6293 0 16) (extract v_6295 0 16)) (concat (concat (extract v_6293 16 32) (extract v_6295 16 32)) (concat (concat (extract v_6293 32 48) (extract v_6295 32 48)) (concat (concat (extract v_6293 48 64) (extract v_6295 48 64)) (concat (concat (extract v_6293 128 144) (extract v_6295 128 144)) (concat (concat (extract v_6293 144 160) (extract v_6295 144 160)) (concat (concat (extract v_6293 160 176) (extract v_6295 160 176)) (concat (extract v_6293 176 192) (extract v_6295 176 192)))))))));
      pure ()
    pat_end;
    pattern fun (v_2731 : Mem) (v_2732 : reg (bv 128)) (v_2733 : reg (bv 128)) => do
      v_12336 <- evaluateAddress v_2731;
      v_12337 <- load v_12336 16;
      v_12339 <- getRegister v_2732;
      setRegister (lhs.of_reg v_2733) (concat (concat (extract v_12337 0 16) (extract v_12339 0 16)) (concat (concat (extract v_12337 16 32) (extract v_12339 16 32)) (concat (concat (extract v_12337 32 48) (extract v_12339 32 48)) (concat (extract v_12337 48 64) (extract v_12339 48 64)))));
      pure ()
    pat_end;
    pattern fun (v_2742 : Mem) (v_2743 : reg (bv 256)) (v_2744 : reg (bv 256)) => do
      v_12355 <- evaluateAddress v_2742;
      v_12356 <- load v_12355 32;
      v_12358 <- getRegister v_2743;
      setRegister (lhs.of_reg v_2744) (concat (concat (extract v_12356 0 16) (extract v_12358 0 16)) (concat (concat (extract v_12356 16 32) (extract v_12358 16 32)) (concat (concat (extract v_12356 32 48) (extract v_12358 32 48)) (concat (concat (extract v_12356 48 64) (extract v_12358 48 64)) (concat (concat (extract v_12356 128 144) (extract v_12358 128 144)) (concat (concat (extract v_12356 144 160) (extract v_12358 144 160)) (concat (concat (extract v_12356 160 176) (extract v_12358 160 176)) (concat (extract v_12356 176 192) (extract v_12358 176 192)))))))));
      pure ()
    pat_end
