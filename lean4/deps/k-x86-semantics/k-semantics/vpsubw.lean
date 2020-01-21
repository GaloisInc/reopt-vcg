def vpsubw : instruction :=
  definst "vpsubw" $ do
    pattern fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) => do
      v_3 <- getRegister (lhs.of_reg xmm_1);
      v_4 <- evaluateAddress mem_0;
      v_5 <- load v_4 16;
      setRegister (lhs.of_reg xmm_2) (concat (sub (extract v_3 0 16) (extract v_5 0 16)) (concat (sub (extract v_3 16 32) (extract v_5 16 32)) (concat (sub (extract v_3 32 48) (extract v_5 32 48)) (concat (sub (extract v_3 48 64) (extract v_5 48 64)) (concat (sub (extract v_3 64 80) (extract v_5 64 80)) (concat (sub (extract v_3 80 96) (extract v_5 80 96)) (concat (sub (extract v_3 96 112) (extract v_5 96 112)) (sub (extract v_3 112 128) (extract v_5 112 128)))))))));
      pure ()
    pat_end;
    pattern fun (mem_0 : Mem) (ymm_1 : reg (bv 256)) (ymm_2 : reg (bv 256)) => do
      v_3 <- getRegister (lhs.of_reg ymm_1);
      v_4 <- evaluateAddress mem_0;
      v_5 <- load v_4 32;
      setRegister (lhs.of_reg ymm_2) (concat (sub (extract v_3 0 16) (extract v_5 0 16)) (concat (sub (extract v_3 16 32) (extract v_5 16 32)) (concat (sub (extract v_3 32 48) (extract v_5 32 48)) (concat (sub (extract v_3 48 64) (extract v_5 48 64)) (concat (sub (extract v_3 64 80) (extract v_5 64 80)) (concat (sub (extract v_3 80 96) (extract v_5 80 96)) (concat (sub (extract v_3 96 112) (extract v_5 96 112)) (concat (sub (extract v_3 112 128) (extract v_5 112 128)) (concat (sub (extract v_3 128 144) (extract v_5 128 144)) (concat (sub (extract v_3 144 160) (extract v_5 144 160)) (concat (sub (extract v_3 160 176) (extract v_5 160 176)) (concat (sub (extract v_3 176 192) (extract v_5 176 192)) (concat (sub (extract v_3 192 208) (extract v_5 192 208)) (concat (sub (extract v_3 208 224) (extract v_5 208 224)) (concat (sub (extract v_3 224 240) (extract v_5 224 240)) (sub (extract v_3 240 256) (extract v_5 240 256)))))))))))))))));
      pure ()
    pat_end;
    pattern fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) => do
      v_3 <- getRegister (lhs.of_reg xmm_1);
      v_4 <- getRegister (lhs.of_reg xmm_0);
      setRegister (lhs.of_reg xmm_2) (concat (sub (extract v_3 0 16) (extract v_4 0 16)) (concat (sub (extract v_3 16 32) (extract v_4 16 32)) (concat (sub (extract v_3 32 48) (extract v_4 32 48)) (concat (sub (extract v_3 48 64) (extract v_4 48 64)) (concat (sub (extract v_3 64 80) (extract v_4 64 80)) (concat (sub (extract v_3 80 96) (extract v_4 80 96)) (concat (sub (extract v_3 96 112) (extract v_4 96 112)) (sub (extract v_3 112 128) (extract v_4 112 128)))))))));
      pure ()
    pat_end;
    pattern fun (ymm_0 : reg (bv 256)) (ymm_1 : reg (bv 256)) (ymm_2 : reg (bv 256)) => do
      v_3 <- getRegister (lhs.of_reg ymm_1);
      v_4 <- getRegister (lhs.of_reg ymm_0);
      setRegister (lhs.of_reg ymm_2) (concat (sub (extract v_3 0 16) (extract v_4 0 16)) (concat (sub (extract v_3 16 32) (extract v_4 16 32)) (concat (sub (extract v_3 32 48) (extract v_4 32 48)) (concat (sub (extract v_3 48 64) (extract v_4 48 64)) (concat (sub (extract v_3 64 80) (extract v_4 64 80)) (concat (sub (extract v_3 80 96) (extract v_4 80 96)) (concat (sub (extract v_3 96 112) (extract v_4 96 112)) (concat (sub (extract v_3 112 128) (extract v_4 112 128)) (concat (sub (extract v_3 128 144) (extract v_4 128 144)) (concat (sub (extract v_3 144 160) (extract v_4 144 160)) (concat (sub (extract v_3 160 176) (extract v_4 160 176)) (concat (sub (extract v_3 176 192) (extract v_4 176 192)) (concat (sub (extract v_3 192 208) (extract v_4 192 208)) (concat (sub (extract v_3 208 224) (extract v_4 208 224)) (concat (sub (extract v_3 224 240) (extract v_4 224 240)) (sub (extract v_3 240 256) (extract v_4 240 256)))))))))))))))));
      pure ()
    pat_end
