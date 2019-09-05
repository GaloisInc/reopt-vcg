def vpunpcklbw1 : instruction :=
  definst "vpunpcklbw" $ do
    pattern fun (v_2732 : reg (bv 128)) (v_2733 : reg (bv 128)) (v_2734 : reg (bv 128)) => do
      v_6305 <- getRegister v_2732;
      v_6307 <- getRegister v_2733;
      setRegister (lhs.of_reg v_2734) (concat (concat (extract v_6305 64 72) (extract v_6307 64 72)) (concat (concat (extract v_6305 72 80) (extract v_6307 72 80)) (concat (concat (extract v_6305 80 88) (extract v_6307 80 88)) (concat (concat (extract v_6305 88 96) (extract v_6307 88 96)) (concat (concat (extract v_6305 96 104) (extract v_6307 96 104)) (concat (concat (extract v_6305 104 112) (extract v_6307 104 112)) (concat (concat (extract v_6305 112 120) (extract v_6307 112 120)) (concat (extract v_6305 120 128) (extract v_6307 120 128)))))))));
      pure ()
    pat_end;
    pattern fun (v_2743 : reg (bv 256)) (v_2744 : reg (bv 256)) (v_2745 : reg (bv 256)) => do
      v_6344 <- getRegister v_2743;
      v_6346 <- getRegister v_2744;
      setRegister (lhs.of_reg v_2745) (concat (concat (extract v_6344 64 72) (extract v_6346 64 72)) (concat (concat (extract v_6344 72 80) (extract v_6346 72 80)) (concat (concat (extract v_6344 80 88) (extract v_6346 80 88)) (concat (concat (extract v_6344 88 96) (extract v_6346 88 96)) (concat (concat (extract v_6344 96 104) (extract v_6346 96 104)) (concat (concat (extract v_6344 104 112) (extract v_6346 104 112)) (concat (concat (extract v_6344 112 120) (extract v_6346 112 120)) (concat (concat (extract v_6344 120 128) (extract v_6346 120 128)) (concat (concat (extract v_6344 192 200) (extract v_6346 192 200)) (concat (concat (extract v_6344 200 208) (extract v_6346 200 208)) (concat (concat (extract v_6344 208 216) (extract v_6346 208 216)) (concat (concat (extract v_6344 216 224) (extract v_6346 216 224)) (concat (concat (extract v_6344 224 232) (extract v_6346 224 232)) (concat (concat (extract v_6344 232 240) (extract v_6346 232 240)) (concat (concat (extract v_6344 240 248) (extract v_6346 240 248)) (concat (extract v_6344 248 256) (extract v_6346 248 256)))))))))))))))));
      pure ()
    pat_end;
    pattern fun (v_2726 : Mem) (v_2727 : reg (bv 128)) (v_2728 : reg (bv 128)) => do
      v_12363 <- evaluateAddress v_2726;
      v_12364 <- load v_12363 16;
      v_12366 <- getRegister v_2727;
      setRegister (lhs.of_reg v_2728) (concat (concat (extract v_12364 64 72) (extract v_12366 64 72)) (concat (concat (extract v_12364 72 80) (extract v_12366 72 80)) (concat (concat (extract v_12364 80 88) (extract v_12366 80 88)) (concat (concat (extract v_12364 88 96) (extract v_12366 88 96)) (concat (concat (extract v_12364 96 104) (extract v_12366 96 104)) (concat (concat (extract v_12364 104 112) (extract v_12366 104 112)) (concat (concat (extract v_12364 112 120) (extract v_12366 112 120)) (concat (extract v_12364 120 128) (extract v_12366 120 128)))))))));
      pure ()
    pat_end;
    pattern fun (v_2737 : Mem) (v_2738 : reg (bv 256)) (v_2739 : reg (bv 256)) => do
      v_12398 <- evaluateAddress v_2737;
      v_12399 <- load v_12398 32;
      v_12401 <- getRegister v_2738;
      setRegister (lhs.of_reg v_2739) (concat (concat (extract v_12399 64 72) (extract v_12401 64 72)) (concat (concat (extract v_12399 72 80) (extract v_12401 72 80)) (concat (concat (extract v_12399 80 88) (extract v_12401 80 88)) (concat (concat (extract v_12399 88 96) (extract v_12401 88 96)) (concat (concat (extract v_12399 96 104) (extract v_12401 96 104)) (concat (concat (extract v_12399 104 112) (extract v_12401 104 112)) (concat (concat (extract v_12399 112 120) (extract v_12401 112 120)) (concat (concat (extract v_12399 120 128) (extract v_12401 120 128)) (concat (concat (extract v_12399 192 200) (extract v_12401 192 200)) (concat (concat (extract v_12399 200 208) (extract v_12401 200 208)) (concat (concat (extract v_12399 208 216) (extract v_12401 208 216)) (concat (concat (extract v_12399 216 224) (extract v_12401 216 224)) (concat (concat (extract v_12399 224 232) (extract v_12401 224 232)) (concat (concat (extract v_12399 232 240) (extract v_12401 232 240)) (concat (concat (extract v_12399 240 248) (extract v_12401 240 248)) (concat (extract v_12399 248 256) (extract v_12401 248 256)))))))))))))))));
      pure ()
    pat_end
