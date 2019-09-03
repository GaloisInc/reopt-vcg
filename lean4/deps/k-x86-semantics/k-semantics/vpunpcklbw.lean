def vpunpcklbw1 : instruction :=
  definst "vpunpcklbw" $ do
    pattern fun (v_2668 : reg (bv 128)) (v_2669 : reg (bv 128)) (v_2670 : reg (bv 128)) => do
      v_6391 <- getRegister v_2668;
      v_6393 <- getRegister v_2669;
      setRegister (lhs.of_reg v_2670) (concat (concat (extract v_6391 64 72) (extract v_6393 64 72)) (concat (concat (extract v_6391 72 80) (extract v_6393 72 80)) (concat (concat (extract v_6391 80 88) (extract v_6393 80 88)) (concat (concat (extract v_6391 88 96) (extract v_6393 88 96)) (concat (concat (extract v_6391 96 104) (extract v_6393 96 104)) (concat (concat (extract v_6391 104 112) (extract v_6393 104 112)) (concat (concat (extract v_6391 112 120) (extract v_6393 112 120)) (concat (extract v_6391 120 128) (extract v_6393 120 128)))))))));
      pure ()
    pat_end;
    pattern fun (v_2678 : reg (bv 256)) (v_2679 : reg (bv 256)) (v_2680 : reg (bv 256)) => do
      v_6430 <- getRegister v_2678;
      v_6432 <- getRegister v_2679;
      setRegister (lhs.of_reg v_2680) (concat (concat (extract v_6430 64 72) (extract v_6432 64 72)) (concat (concat (extract v_6430 72 80) (extract v_6432 72 80)) (concat (concat (extract v_6430 80 88) (extract v_6432 80 88)) (concat (concat (extract v_6430 88 96) (extract v_6432 88 96)) (concat (concat (extract v_6430 96 104) (extract v_6432 96 104)) (concat (concat (extract v_6430 104 112) (extract v_6432 104 112)) (concat (concat (extract v_6430 112 120) (extract v_6432 112 120)) (concat (concat (extract v_6430 120 128) (extract v_6432 120 128)) (concat (concat (extract v_6430 192 200) (extract v_6432 192 200)) (concat (concat (extract v_6430 200 208) (extract v_6432 200 208)) (concat (concat (extract v_6430 208 216) (extract v_6432 208 216)) (concat (concat (extract v_6430 216 224) (extract v_6432 216 224)) (concat (concat (extract v_6430 224 232) (extract v_6432 224 232)) (concat (concat (extract v_6430 232 240) (extract v_6432 232 240)) (concat (concat (extract v_6430 240 248) (extract v_6432 240 248)) (concat (extract v_6430 248 256) (extract v_6432 248 256)))))))))))))))));
      pure ()
    pat_end;
    pattern fun (v_2662 : Mem) (v_2663 : reg (bv 128)) (v_2664 : reg (bv 128)) => do
      v_12690 <- evaluateAddress v_2662;
      v_12691 <- load v_12690 16;
      v_12693 <- getRegister v_2663;
      setRegister (lhs.of_reg v_2664) (concat (concat (extract v_12691 64 72) (extract v_12693 64 72)) (concat (concat (extract v_12691 72 80) (extract v_12693 72 80)) (concat (concat (extract v_12691 80 88) (extract v_12693 80 88)) (concat (concat (extract v_12691 88 96) (extract v_12693 88 96)) (concat (concat (extract v_12691 96 104) (extract v_12693 96 104)) (concat (concat (extract v_12691 104 112) (extract v_12693 104 112)) (concat (concat (extract v_12691 112 120) (extract v_12693 112 120)) (concat (extract v_12691 120 128) (extract v_12693 120 128)))))))));
      pure ()
    pat_end;
    pattern fun (v_2673 : Mem) (v_2674 : reg (bv 256)) (v_2675 : reg (bv 256)) => do
      v_12725 <- evaluateAddress v_2673;
      v_12726 <- load v_12725 32;
      v_12728 <- getRegister v_2674;
      setRegister (lhs.of_reg v_2675) (concat (concat (extract v_12726 64 72) (extract v_12728 64 72)) (concat (concat (extract v_12726 72 80) (extract v_12728 72 80)) (concat (concat (extract v_12726 80 88) (extract v_12728 80 88)) (concat (concat (extract v_12726 88 96) (extract v_12728 88 96)) (concat (concat (extract v_12726 96 104) (extract v_12728 96 104)) (concat (concat (extract v_12726 104 112) (extract v_12728 104 112)) (concat (concat (extract v_12726 112 120) (extract v_12728 112 120)) (concat (concat (extract v_12726 120 128) (extract v_12728 120 128)) (concat (concat (extract v_12726 192 200) (extract v_12728 192 200)) (concat (concat (extract v_12726 200 208) (extract v_12728 200 208)) (concat (concat (extract v_12726 208 216) (extract v_12728 208 216)) (concat (concat (extract v_12726 216 224) (extract v_12728 216 224)) (concat (concat (extract v_12726 224 232) (extract v_12728 224 232)) (concat (concat (extract v_12726 232 240) (extract v_12728 232 240)) (concat (concat (extract v_12726 240 248) (extract v_12728 240 248)) (concat (extract v_12726 248 256) (extract v_12728 248 256)))))))))))))))));
      pure ()
    pat_end
