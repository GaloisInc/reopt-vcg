def vpunpcklwd1 : instruction :=
  definst "vpunpcklwd" $ do
    pattern fun (v_2798 : reg (bv 128)) (v_2799 : reg (bv 128)) (v_2800 : reg (bv 128)) => do
      v_6479 <- getRegister v_2798;
      v_6481 <- getRegister v_2799;
      setRegister (lhs.of_reg v_2800) (concat (concat (extract v_6479 64 80) (extract v_6481 64 80)) (concat (concat (extract v_6479 80 96) (extract v_6481 80 96)) (concat (concat (extract v_6479 96 112) (extract v_6481 96 112)) (concat (extract v_6479 112 128) (extract v_6481 112 128)))));
      pure ()
    pat_end;
    pattern fun (v_2809 : reg (bv 256)) (v_2810 : reg (bv 256)) (v_2811 : reg (bv 256)) => do
      v_6502 <- getRegister v_2809;
      v_6504 <- getRegister v_2810;
      setRegister (lhs.of_reg v_2811) (concat (concat (extract v_6502 64 80) (extract v_6504 64 80)) (concat (concat (extract v_6502 80 96) (extract v_6504 80 96)) (concat (concat (extract v_6502 96 112) (extract v_6504 96 112)) (concat (concat (extract v_6502 112 128) (extract v_6504 112 128)) (concat (concat (extract v_6502 192 208) (extract v_6504 192 208)) (concat (concat (extract v_6502 208 224) (extract v_6504 208 224)) (concat (concat (extract v_6502 224 240) (extract v_6504 224 240)) (concat (extract v_6502 240 256) (extract v_6504 240 256)))))))));
      pure ()
    pat_end;
    pattern fun (v_2792 : Mem) (v_2793 : reg (bv 128)) (v_2794 : reg (bv 128)) => do
      v_12513 <- evaluateAddress v_2792;
      v_12514 <- load v_12513 16;
      v_12516 <- getRegister v_2793;
      setRegister (lhs.of_reg v_2794) (concat (concat (extract v_12514 64 80) (extract v_12516 64 80)) (concat (concat (extract v_12514 80 96) (extract v_12516 80 96)) (concat (concat (extract v_12514 96 112) (extract v_12516 96 112)) (concat (extract v_12514 112 128) (extract v_12516 112 128)))));
      pure ()
    pat_end;
    pattern fun (v_2803 : Mem) (v_2804 : reg (bv 256)) (v_2805 : reg (bv 256)) => do
      v_12532 <- evaluateAddress v_2803;
      v_12533 <- load v_12532 32;
      v_12535 <- getRegister v_2804;
      setRegister (lhs.of_reg v_2805) (concat (concat (extract v_12533 64 80) (extract v_12535 64 80)) (concat (concat (extract v_12533 80 96) (extract v_12535 80 96)) (concat (concat (extract v_12533 96 112) (extract v_12535 96 112)) (concat (concat (extract v_12533 112 128) (extract v_12535 112 128)) (concat (concat (extract v_12533 192 208) (extract v_12535 192 208)) (concat (concat (extract v_12533 208 224) (extract v_12535 208 224)) (concat (concat (extract v_12533 224 240) (extract v_12535 224 240)) (concat (extract v_12533 240 256) (extract v_12535 240 256)))))))));
      pure ()
    pat_end
