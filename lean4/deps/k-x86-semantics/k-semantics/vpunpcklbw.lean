def vpunpcklbw1 : instruction :=
  definst "vpunpcklbw" $ do
    pattern fun (v_2678 : reg (bv 128)) (v_2679 : reg (bv 128)) (v_2680 : reg (bv 128)) => do
      v_6256 <- getRegister v_2678;
      v_6258 <- getRegister v_2679;
      setRegister (lhs.of_reg v_2680) (concat (concat (extract v_6256 64 72) (extract v_6258 64 72)) (concat (concat (extract v_6256 72 80) (extract v_6258 72 80)) (concat (concat (extract v_6256 80 88) (extract v_6258 80 88)) (concat (concat (extract v_6256 88 96) (extract v_6258 88 96)) (concat (concat (extract v_6256 96 104) (extract v_6258 96 104)) (concat (concat (extract v_6256 104 112) (extract v_6258 104 112)) (concat (concat (extract v_6256 112 120) (extract v_6258 112 120)) (concat (extract v_6256 120 128) (extract v_6258 120 128)))))))));
      pure ()
    pat_end;
    pattern fun (v_2689 : reg (bv 256)) (v_2690 : reg (bv 256)) (v_2691 : reg (bv 256)) => do
      v_6295 <- getRegister v_2689;
      v_6297 <- getRegister v_2690;
      setRegister (lhs.of_reg v_2691) (concat (concat (extract v_6295 64 72) (extract v_6297 64 72)) (concat (concat (extract v_6295 72 80) (extract v_6297 72 80)) (concat (concat (extract v_6295 80 88) (extract v_6297 80 88)) (concat (concat (extract v_6295 88 96) (extract v_6297 88 96)) (concat (concat (extract v_6295 96 104) (extract v_6297 96 104)) (concat (concat (extract v_6295 104 112) (extract v_6297 104 112)) (concat (concat (extract v_6295 112 120) (extract v_6297 112 120)) (concat (concat (extract v_6295 120 128) (extract v_6297 120 128)) (concat (concat (extract v_6295 192 200) (extract v_6297 192 200)) (concat (concat (extract v_6295 200 208) (extract v_6297 200 208)) (concat (concat (extract v_6295 208 216) (extract v_6297 208 216)) (concat (concat (extract v_6295 216 224) (extract v_6297 216 224)) (concat (concat (extract v_6295 224 232) (extract v_6297 224 232)) (concat (concat (extract v_6295 232 240) (extract v_6297 232 240)) (concat (concat (extract v_6295 240 248) (extract v_6297 240 248)) (concat (extract v_6295 248 256) (extract v_6297 248 256)))))))))))))))));
      pure ()
    pat_end;
    pattern fun (v_2673 : Mem) (v_2674 : reg (bv 128)) (v_2675 : reg (bv 128)) => do
      v_12687 <- evaluateAddress v_2673;
      v_12688 <- load v_12687 16;
      v_12690 <- getRegister v_2674;
      setRegister (lhs.of_reg v_2675) (concat (concat (extract v_12688 64 72) (extract v_12690 64 72)) (concat (concat (extract v_12688 72 80) (extract v_12690 72 80)) (concat (concat (extract v_12688 80 88) (extract v_12690 80 88)) (concat (concat (extract v_12688 88 96) (extract v_12690 88 96)) (concat (concat (extract v_12688 96 104) (extract v_12690 96 104)) (concat (concat (extract v_12688 104 112) (extract v_12690 104 112)) (concat (concat (extract v_12688 112 120) (extract v_12690 112 120)) (concat (extract v_12688 120 128) (extract v_12690 120 128)))))))));
      pure ()
    pat_end;
    pattern fun (v_2684 : Mem) (v_2685 : reg (bv 256)) (v_2686 : reg (bv 256)) => do
      v_12722 <- evaluateAddress v_2684;
      v_12723 <- load v_12722 32;
      v_12725 <- getRegister v_2685;
      setRegister (lhs.of_reg v_2686) (concat (concat (extract v_12723 64 72) (extract v_12725 64 72)) (concat (concat (extract v_12723 72 80) (extract v_12725 72 80)) (concat (concat (extract v_12723 80 88) (extract v_12725 80 88)) (concat (concat (extract v_12723 88 96) (extract v_12725 88 96)) (concat (concat (extract v_12723 96 104) (extract v_12725 96 104)) (concat (concat (extract v_12723 104 112) (extract v_12725 104 112)) (concat (concat (extract v_12723 112 120) (extract v_12725 112 120)) (concat (concat (extract v_12723 120 128) (extract v_12725 120 128)) (concat (concat (extract v_12723 192 200) (extract v_12725 192 200)) (concat (concat (extract v_12723 200 208) (extract v_12725 200 208)) (concat (concat (extract v_12723 208 216) (extract v_12725 208 216)) (concat (concat (extract v_12723 216 224) (extract v_12725 216 224)) (concat (concat (extract v_12723 224 232) (extract v_12725 224 232)) (concat (concat (extract v_12723 232 240) (extract v_12725 232 240)) (concat (concat (extract v_12723 240 248) (extract v_12725 240 248)) (concat (extract v_12723 248 256) (extract v_12725 248 256)))))))))))))))));
      pure ()
    pat_end
