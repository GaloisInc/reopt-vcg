def vpunpcklbw1 : instruction :=
  definst "vpunpcklbw" $ do
    pattern fun (v_2759 : reg (bv 128)) (v_2760 : reg (bv 128)) (v_2761 : reg (bv 128)) => do
      v_6332 <- getRegister v_2759;
      v_6334 <- getRegister v_2760;
      setRegister (lhs.of_reg v_2761) (concat (concat (extract v_6332 64 72) (extract v_6334 64 72)) (concat (concat (extract v_6332 72 80) (extract v_6334 72 80)) (concat (concat (extract v_6332 80 88) (extract v_6334 80 88)) (concat (concat (extract v_6332 88 96) (extract v_6334 88 96)) (concat (concat (extract v_6332 96 104) (extract v_6334 96 104)) (concat (concat (extract v_6332 104 112) (extract v_6334 104 112)) (concat (concat (extract v_6332 112 120) (extract v_6334 112 120)) (concat (extract v_6332 120 128) (extract v_6334 120 128)))))))));
      pure ()
    pat_end;
    pattern fun (v_2770 : reg (bv 256)) (v_2771 : reg (bv 256)) (v_2772 : reg (bv 256)) => do
      v_6371 <- getRegister v_2770;
      v_6373 <- getRegister v_2771;
      setRegister (lhs.of_reg v_2772) (concat (concat (extract v_6371 64 72) (extract v_6373 64 72)) (concat (concat (extract v_6371 72 80) (extract v_6373 72 80)) (concat (concat (extract v_6371 80 88) (extract v_6373 80 88)) (concat (concat (extract v_6371 88 96) (extract v_6373 88 96)) (concat (concat (extract v_6371 96 104) (extract v_6373 96 104)) (concat (concat (extract v_6371 104 112) (extract v_6373 104 112)) (concat (concat (extract v_6371 112 120) (extract v_6373 112 120)) (concat (concat (extract v_6371 120 128) (extract v_6373 120 128)) (concat (concat (extract v_6371 192 200) (extract v_6373 192 200)) (concat (concat (extract v_6371 200 208) (extract v_6373 200 208)) (concat (concat (extract v_6371 208 216) (extract v_6373 208 216)) (concat (concat (extract v_6371 216 224) (extract v_6373 216 224)) (concat (concat (extract v_6371 224 232) (extract v_6373 224 232)) (concat (concat (extract v_6371 232 240) (extract v_6373 232 240)) (concat (concat (extract v_6371 240 248) (extract v_6373 240 248)) (concat (extract v_6371 248 256) (extract v_6373 248 256)))))))))))))))));
      pure ()
    pat_end;
    pattern fun (v_2753 : Mem) (v_2754 : reg (bv 128)) (v_2755 : reg (bv 128)) => do
      v_12390 <- evaluateAddress v_2753;
      v_12391 <- load v_12390 16;
      v_12393 <- getRegister v_2754;
      setRegister (lhs.of_reg v_2755) (concat (concat (extract v_12391 64 72) (extract v_12393 64 72)) (concat (concat (extract v_12391 72 80) (extract v_12393 72 80)) (concat (concat (extract v_12391 80 88) (extract v_12393 80 88)) (concat (concat (extract v_12391 88 96) (extract v_12393 88 96)) (concat (concat (extract v_12391 96 104) (extract v_12393 96 104)) (concat (concat (extract v_12391 104 112) (extract v_12393 104 112)) (concat (concat (extract v_12391 112 120) (extract v_12393 112 120)) (concat (extract v_12391 120 128) (extract v_12393 120 128)))))))));
      pure ()
    pat_end;
    pattern fun (v_2764 : Mem) (v_2765 : reg (bv 256)) (v_2766 : reg (bv 256)) => do
      v_12425 <- evaluateAddress v_2764;
      v_12426 <- load v_12425 32;
      v_12428 <- getRegister v_2765;
      setRegister (lhs.of_reg v_2766) (concat (concat (extract v_12426 64 72) (extract v_12428 64 72)) (concat (concat (extract v_12426 72 80) (extract v_12428 72 80)) (concat (concat (extract v_12426 80 88) (extract v_12428 80 88)) (concat (concat (extract v_12426 88 96) (extract v_12428 88 96)) (concat (concat (extract v_12426 96 104) (extract v_12428 96 104)) (concat (concat (extract v_12426 104 112) (extract v_12428 104 112)) (concat (concat (extract v_12426 112 120) (extract v_12428 112 120)) (concat (concat (extract v_12426 120 128) (extract v_12428 120 128)) (concat (concat (extract v_12426 192 200) (extract v_12428 192 200)) (concat (concat (extract v_12426 200 208) (extract v_12428 200 208)) (concat (concat (extract v_12426 208 216) (extract v_12428 208 216)) (concat (concat (extract v_12426 216 224) (extract v_12428 216 224)) (concat (concat (extract v_12426 224 232) (extract v_12428 224 232)) (concat (concat (extract v_12426 232 240) (extract v_12428 232 240)) (concat (concat (extract v_12426 240 248) (extract v_12428 240 248)) (concat (extract v_12426 248 256) (extract v_12428 248 256)))))))))))))))));
      pure ()
    pat_end
