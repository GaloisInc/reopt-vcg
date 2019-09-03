def vpunpckhwd1 : instruction :=
  definst "vpunpckhwd" $ do
    pattern fun (v_2646 : reg (bv 128)) (v_2647 : reg (bv 128)) (v_2648 : reg (bv 128)) => do
      v_6329 <- getRegister v_2646;
      v_6331 <- getRegister v_2647;
      setRegister (lhs.of_reg v_2648) (concat (concat (extract v_6329 0 16) (extract v_6331 0 16)) (concat (concat (extract v_6329 16 32) (extract v_6331 16 32)) (concat (concat (extract v_6329 32 48) (extract v_6331 32 48)) (concat (extract v_6329 48 64) (extract v_6331 48 64)))));
      pure ()
    pat_end;
    pattern fun (v_2656 : reg (bv 256)) (v_2657 : reg (bv 256)) (v_2658 : reg (bv 256)) => do
      v_6352 <- getRegister v_2656;
      v_6354 <- getRegister v_2657;
      setRegister (lhs.of_reg v_2658) (concat (concat (extract v_6352 0 16) (extract v_6354 0 16)) (concat (concat (extract v_6352 16 32) (extract v_6354 16 32)) (concat (concat (extract v_6352 32 48) (extract v_6354 32 48)) (concat (concat (extract v_6352 48 64) (extract v_6354 48 64)) (concat (concat (extract v_6352 128 144) (extract v_6354 128 144)) (concat (concat (extract v_6352 144 160) (extract v_6354 144 160)) (concat (concat (extract v_6352 160 176) (extract v_6354 160 176)) (concat (extract v_6352 176 192) (extract v_6354 176 192)))))))));
      pure ()
    pat_end;
    pattern fun (v_2640 : Mem) (v_2641 : reg (bv 128)) (v_2642 : reg (bv 128)) => do
      v_12636 <- evaluateAddress v_2640;
      v_12637 <- load v_12636 16;
      v_12639 <- getRegister v_2641;
      setRegister (lhs.of_reg v_2642) (concat (concat (extract v_12637 0 16) (extract v_12639 0 16)) (concat (concat (extract v_12637 16 32) (extract v_12639 16 32)) (concat (concat (extract v_12637 32 48) (extract v_12639 32 48)) (concat (extract v_12637 48 64) (extract v_12639 48 64)))));
      pure ()
    pat_end;
    pattern fun (v_2651 : Mem) (v_2652 : reg (bv 256)) (v_2653 : reg (bv 256)) => do
      v_12655 <- evaluateAddress v_2651;
      v_12656 <- load v_12655 32;
      v_12658 <- getRegister v_2652;
      setRegister (lhs.of_reg v_2653) (concat (concat (extract v_12656 0 16) (extract v_12658 0 16)) (concat (concat (extract v_12656 16 32) (extract v_12658 16 32)) (concat (concat (extract v_12656 32 48) (extract v_12658 32 48)) (concat (concat (extract v_12656 48 64) (extract v_12658 48 64)) (concat (concat (extract v_12656 128 144) (extract v_12658 128 144)) (concat (concat (extract v_12656 144 160) (extract v_12658 144 160)) (concat (concat (extract v_12656 160 176) (extract v_12658 160 176)) (concat (extract v_12656 176 192) (extract v_12658 176 192)))))))));
      pure ()
    pat_end
