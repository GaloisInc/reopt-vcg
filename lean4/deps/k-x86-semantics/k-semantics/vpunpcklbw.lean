def vpunpcklbw : instruction :=
  definst "vpunpcklbw" $ do
    pattern fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) => do
      v_3 <- evaluateAddress mem_0;
      v_4 <- load v_3 16;
      v_5 <- getRegister (lhs.of_reg xmm_1);
      setRegister (lhs.of_reg xmm_2) (concat (concat (extract v_4 64 72) (extract v_5 64 72)) (concat (concat (extract v_4 72 80) (extract v_5 72 80)) (concat (concat (extract v_4 80 88) (extract v_5 80 88)) (concat (concat (extract v_4 88 96) (extract v_5 88 96)) (concat (concat (extract v_4 96 104) (extract v_5 96 104)) (concat (concat (extract v_4 104 112) (extract v_5 104 112)) (concat (concat (extract v_4 112 120) (extract v_5 112 120)) (concat (extract v_4 120 128) (extract v_5 120 128)))))))));
      pure ()
    pat_end;
    pattern fun (mem_0 : Mem) (ymm_1 : reg (bv 256)) (ymm_2 : reg (bv 256)) => do
      v_3 <- evaluateAddress mem_0;
      v_4 <- load v_3 32;
      v_5 <- getRegister (lhs.of_reg ymm_1);
      setRegister (lhs.of_reg ymm_2) (concat (concat (extract v_4 64 72) (extract v_5 64 72)) (concat (concat (extract v_4 72 80) (extract v_5 72 80)) (concat (concat (extract v_4 80 88) (extract v_5 80 88)) (concat (concat (extract v_4 88 96) (extract v_5 88 96)) (concat (concat (extract v_4 96 104) (extract v_5 96 104)) (concat (concat (extract v_4 104 112) (extract v_5 104 112)) (concat (concat (extract v_4 112 120) (extract v_5 112 120)) (concat (concat (extract v_4 120 128) (extract v_5 120 128)) (concat (concat (extract v_4 192 200) (extract v_5 192 200)) (concat (concat (extract v_4 200 208) (extract v_5 200 208)) (concat (concat (extract v_4 208 216) (extract v_5 208 216)) (concat (concat (extract v_4 216 224) (extract v_5 216 224)) (concat (concat (extract v_4 224 232) (extract v_5 224 232)) (concat (concat (extract v_4 232 240) (extract v_5 232 240)) (concat (concat (extract v_4 240 248) (extract v_5 240 248)) (concat (extract v_4 248 256) (extract v_5 248 256)))))))))))))))));
      pure ()
    pat_end;
    pattern fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) => do
      v_3 <- getRegister (lhs.of_reg xmm_0);
      v_4 <- getRegister (lhs.of_reg xmm_1);
      setRegister (lhs.of_reg xmm_2) (concat (concat (extract v_3 64 72) (extract v_4 64 72)) (concat (concat (extract v_3 72 80) (extract v_4 72 80)) (concat (concat (extract v_3 80 88) (extract v_4 80 88)) (concat (concat (extract v_3 88 96) (extract v_4 88 96)) (concat (concat (extract v_3 96 104) (extract v_4 96 104)) (concat (concat (extract v_3 104 112) (extract v_4 104 112)) (concat (concat (extract v_3 112 120) (extract v_4 112 120)) (concat (extract v_3 120 128) (extract v_4 120 128)))))))));
      pure ()
    pat_end;
    pattern fun (ymm_0 : reg (bv 256)) (ymm_1 : reg (bv 256)) (ymm_2 : reg (bv 256)) => do
      v_3 <- getRegister (lhs.of_reg ymm_0);
      v_4 <- getRegister (lhs.of_reg ymm_1);
      setRegister (lhs.of_reg ymm_2) (concat (concat (extract v_3 64 72) (extract v_4 64 72)) (concat (concat (extract v_3 72 80) (extract v_4 72 80)) (concat (concat (extract v_3 80 88) (extract v_4 80 88)) (concat (concat (extract v_3 88 96) (extract v_4 88 96)) (concat (concat (extract v_3 96 104) (extract v_4 96 104)) (concat (concat (extract v_3 104 112) (extract v_4 104 112)) (concat (concat (extract v_3 112 120) (extract v_4 112 120)) (concat (concat (extract v_3 120 128) (extract v_4 120 128)) (concat (concat (extract v_3 192 200) (extract v_4 192 200)) (concat (concat (extract v_3 200 208) (extract v_4 200 208)) (concat (concat (extract v_3 208 216) (extract v_4 208 216)) (concat (concat (extract v_3 216 224) (extract v_4 216 224)) (concat (concat (extract v_3 224 232) (extract v_4 224 232)) (concat (concat (extract v_3 232 240) (extract v_4 232 240)) (concat (concat (extract v_3 240 248) (extract v_4 240 248)) (concat (extract v_3 248 256) (extract v_4 248 256)))))))))))))))));
      pure ()
    pat_end
