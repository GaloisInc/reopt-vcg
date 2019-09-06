def vpunpcklwd1 : instruction :=
  definst "vpunpcklwd" $ do
    pattern fun (v_2825 : reg (bv 128)) (v_2826 : reg (bv 128)) (v_2827 : reg (bv 128)) => do
      v_6506 <- getRegister v_2825;
      v_6508 <- getRegister v_2826;
      setRegister (lhs.of_reg v_2827) (concat (concat (extract v_6506 64 80) (extract v_6508 64 80)) (concat (concat (extract v_6506 80 96) (extract v_6508 80 96)) (concat (concat (extract v_6506 96 112) (extract v_6508 96 112)) (concat (extract v_6506 112 128) (extract v_6508 112 128)))));
      pure ()
    pat_end;
    pattern fun (v_2836 : reg (bv 256)) (v_2837 : reg (bv 256)) (v_2838 : reg (bv 256)) => do
      v_6529 <- getRegister v_2836;
      v_6531 <- getRegister v_2837;
      setRegister (lhs.of_reg v_2838) (concat (concat (extract v_6529 64 80) (extract v_6531 64 80)) (concat (concat (extract v_6529 80 96) (extract v_6531 80 96)) (concat (concat (extract v_6529 96 112) (extract v_6531 96 112)) (concat (concat (extract v_6529 112 128) (extract v_6531 112 128)) (concat (concat (extract v_6529 192 208) (extract v_6531 192 208)) (concat (concat (extract v_6529 208 224) (extract v_6531 208 224)) (concat (concat (extract v_6529 224 240) (extract v_6531 224 240)) (concat (extract v_6529 240 256) (extract v_6531 240 256)))))))));
      pure ()
    pat_end;
    pattern fun (v_2819 : Mem) (v_2820 : reg (bv 128)) (v_2821 : reg (bv 128)) => do
      v_12540 <- evaluateAddress v_2819;
      v_12541 <- load v_12540 16;
      v_12543 <- getRegister v_2820;
      setRegister (lhs.of_reg v_2821) (concat (concat (extract v_12541 64 80) (extract v_12543 64 80)) (concat (concat (extract v_12541 80 96) (extract v_12543 80 96)) (concat (concat (extract v_12541 96 112) (extract v_12543 96 112)) (concat (extract v_12541 112 128) (extract v_12543 112 128)))));
      pure ()
    pat_end;
    pattern fun (v_2830 : Mem) (v_2831 : reg (bv 256)) (v_2832 : reg (bv 256)) => do
      v_12559 <- evaluateAddress v_2830;
      v_12560 <- load v_12559 32;
      v_12562 <- getRegister v_2831;
      setRegister (lhs.of_reg v_2832) (concat (concat (extract v_12560 64 80) (extract v_12562 64 80)) (concat (concat (extract v_12560 80 96) (extract v_12562 80 96)) (concat (concat (extract v_12560 96 112) (extract v_12562 96 112)) (concat (concat (extract v_12560 112 128) (extract v_12562 112 128)) (concat (concat (extract v_12560 192 208) (extract v_12562 192 208)) (concat (concat (extract v_12560 208 224) (extract v_12562 208 224)) (concat (concat (extract v_12560 224 240) (extract v_12562 224 240)) (concat (extract v_12560 240 256) (extract v_12562 240 256)))))))));
      pure ()
    pat_end
