def vpblendw : instruction :=
  definst "vpblendw" $ do
    pattern fun (imm_0 : imm int) (mem_1 : Mem) (xmm_2 : reg (bv 128)) (xmm_3 : reg (bv 128)) => do
      v_4 <- eval (handleImmediateWithSignExtend imm_0 8 8);
      v_5 <- getRegister (lhs.of_reg xmm_2);
      v_6 <- evaluateAddress mem_1;
      v_7 <- load v_6 16;
      setRegister (lhs.of_reg xmm_3) (concat (mux (isBitClear v_4 0) (extract v_5 0 16) (extract v_7 0 16)) (concat (mux (isBitClear v_4 1) (extract v_5 16 32) (extract v_7 16 32)) (concat (mux (isBitClear v_4 2) (extract v_5 32 48) (extract v_7 32 48)) (concat (mux (isBitClear v_4 3) (extract v_5 48 64) (extract v_7 48 64)) (concat (mux (isBitClear v_4 4) (extract v_5 64 80) (extract v_7 64 80)) (concat (mux (isBitClear v_4 5) (extract v_5 80 96) (extract v_7 80 96)) (concat (mux (isBitClear v_4 6) (extract v_5 96 112) (extract v_7 96 112)) (mux (isBitClear v_4 7) (extract v_5 112 128) (extract v_7 112 128)))))))));
      pure ()
    pat_end;
    pattern fun (imm_0 : imm int) (mem_1 : Mem) (ymm_2 : reg (bv 256)) (ymm_3 : reg (bv 256)) => do
      v_4 <- eval (handleImmediateWithSignExtend imm_0 8 8);
      v_5 <- eval (isBitClear v_4 0);
      v_6 <- getRegister (lhs.of_reg ymm_2);
      v_7 <- evaluateAddress mem_1;
      v_8 <- load v_7 32;
      v_9 <- eval (isBitClear v_4 1);
      v_10 <- eval (isBitClear v_4 2);
      v_11 <- eval (isBitClear v_4 3);
      v_12 <- eval (isBitClear v_4 4);
      v_13 <- eval (isBitClear v_4 5);
      v_14 <- eval (isBitClear v_4 6);
      v_15 <- eval (isBitClear v_4 7);
      setRegister (lhs.of_reg ymm_3) (concat (mux v_5 (extract v_6 0 16) (extract v_8 0 16)) (concat (mux v_9 (extract v_6 16 32) (extract v_8 16 32)) (concat (mux v_10 (extract v_6 32 48) (extract v_8 32 48)) (concat (mux v_11 (extract v_6 48 64) (extract v_8 48 64)) (concat (mux v_12 (extract v_6 64 80) (extract v_8 64 80)) (concat (mux v_13 (extract v_6 80 96) (extract v_8 80 96)) (concat (mux v_14 (extract v_6 96 112) (extract v_8 96 112)) (concat (mux v_15 (extract v_6 112 128) (extract v_8 112 128)) (concat (mux v_5 (extract v_6 128 144) (extract v_8 128 144)) (concat (mux v_9 (extract v_6 144 160) (extract v_8 144 160)) (concat (mux v_10 (extract v_6 160 176) (extract v_8 160 176)) (concat (mux v_11 (extract v_6 176 192) (extract v_8 176 192)) (concat (mux v_12 (extract v_6 192 208) (extract v_8 192 208)) (concat (mux v_13 (extract v_6 208 224) (extract v_8 208 224)) (concat (mux v_14 (extract v_6 224 240) (extract v_8 224 240)) (mux v_15 (extract v_6 240 256) (extract v_8 240 256)))))))))))))))));
      pure ()
    pat_end;
    pattern fun (imm_0 : imm int) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) (xmm_3 : reg (bv 128)) => do
      v_4 <- eval (handleImmediateWithSignExtend imm_0 8 8);
      v_5 <- getRegister (lhs.of_reg xmm_2);
      v_6 <- getRegister (lhs.of_reg xmm_1);
      setRegister (lhs.of_reg xmm_3) (concat (mux (isBitClear v_4 0) (extract v_5 0 16) (extract v_6 0 16)) (concat (mux (isBitClear v_4 1) (extract v_5 16 32) (extract v_6 16 32)) (concat (mux (isBitClear v_4 2) (extract v_5 32 48) (extract v_6 32 48)) (concat (mux (isBitClear v_4 3) (extract v_5 48 64) (extract v_6 48 64)) (concat (mux (isBitClear v_4 4) (extract v_5 64 80) (extract v_6 64 80)) (concat (mux (isBitClear v_4 5) (extract v_5 80 96) (extract v_6 80 96)) (concat (mux (isBitClear v_4 6) (extract v_5 96 112) (extract v_6 96 112)) (mux (isBitClear v_4 7) (extract v_5 112 128) (extract v_6 112 128)))))))));
      pure ()
    pat_end;
    pattern fun (imm_0 : imm int) (ymm_1 : reg (bv 256)) (ymm_2 : reg (bv 256)) (ymm_3 : reg (bv 256)) => do
      v_4 <- eval (handleImmediateWithSignExtend imm_0 8 8);
      v_5 <- eval (isBitClear v_4 0);
      v_6 <- getRegister (lhs.of_reg ymm_2);
      v_7 <- getRegister (lhs.of_reg ymm_1);
      v_8 <- eval (isBitClear v_4 1);
      v_9 <- eval (isBitClear v_4 2);
      v_10 <- eval (isBitClear v_4 3);
      v_11 <- eval (isBitClear v_4 4);
      v_12 <- eval (isBitClear v_4 5);
      v_13 <- eval (isBitClear v_4 6);
      v_14 <- eval (isBitClear v_4 7);
      setRegister (lhs.of_reg ymm_3) (concat (mux v_5 (extract v_6 0 16) (extract v_7 0 16)) (concat (mux v_8 (extract v_6 16 32) (extract v_7 16 32)) (concat (mux v_9 (extract v_6 32 48) (extract v_7 32 48)) (concat (mux v_10 (extract v_6 48 64) (extract v_7 48 64)) (concat (mux v_11 (extract v_6 64 80) (extract v_7 64 80)) (concat (mux v_12 (extract v_6 80 96) (extract v_7 80 96)) (concat (mux v_13 (extract v_6 96 112) (extract v_7 96 112)) (concat (mux v_14 (extract v_6 112 128) (extract v_7 112 128)) (concat (mux v_5 (extract v_6 128 144) (extract v_7 128 144)) (concat (mux v_8 (extract v_6 144 160) (extract v_7 144 160)) (concat (mux v_9 (extract v_6 160 176) (extract v_7 160 176)) (concat (mux v_10 (extract v_6 176 192) (extract v_7 176 192)) (concat (mux v_11 (extract v_6 192 208) (extract v_7 192 208)) (concat (mux v_12 (extract v_6 208 224) (extract v_7 208 224)) (concat (mux v_13 (extract v_6 224 240) (extract v_7 224 240)) (mux v_14 (extract v_6 240 256) (extract v_7 240 256)))))))))))))))));
      pure ()
    pat_end
