def vblendps1 : instruction :=
  definst "vblendps" $ do
    pattern fun (imm_0 : imm int) (mem_1 : Mem) (xmm_2 : reg (bv 128)) (xmm_3 : reg (bv 128)) => do
      v_4 <- eval (handleImmediateWithSignExtend imm_0 8 8);
      v_5 <- getRegister xmm_2;
      v_6 <- evaluateAddress mem_1;
      v_7 <- load v_6 16;
      setRegister (lhs.of_reg xmm_3) (concat (mux (isBitClear v_4 4) (extract v_5 0 32) (extract v_7 0 32)) (concat (mux (isBitClear v_4 5) (extract v_5 32 64) (extract v_7 32 64)) (concat (mux (isBitClear v_4 6) (extract v_5 64 96) (extract v_7 64 96)) (mux (isBitClear v_4 7) (extract v_5 96 128) (extract v_7 96 128)))));
      pure ()
    pat_end;
    pattern fun (imm_0 : imm int) (mem_1 : Mem) (ymm_2 : reg (bv 256)) (ymm_3 : reg (bv 256)) => do
      v_4 <- eval (handleImmediateWithSignExtend imm_0 8 8);
      v_5 <- getRegister ymm_2;
      v_6 <- evaluateAddress mem_1;
      v_7 <- load v_6 32;
      setRegister (lhs.of_reg ymm_3) (concat (mux (isBitClear v_4 0) (extract v_5 0 32) (extract v_7 0 32)) (concat (mux (isBitClear v_4 1) (extract v_5 32 64) (extract v_7 32 64)) (concat (mux (isBitClear v_4 2) (extract v_5 64 96) (extract v_7 64 96)) (concat (mux (isBitClear v_4 3) (extract v_5 96 128) (extract v_7 96 128)) (concat (mux (isBitClear v_4 4) (extract v_5 128 160) (extract v_7 128 160)) (concat (mux (isBitClear v_4 5) (extract v_5 160 192) (extract v_7 160 192)) (concat (mux (isBitClear v_4 6) (extract v_5 192 224) (extract v_7 192 224)) (mux (isBitClear v_4 7) (extract v_5 224 256) (extract v_7 224 256)))))))));
      pure ()
    pat_end;
    pattern fun (imm_0 : imm int) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) (xmm_3 : reg (bv 128)) => do
      v_4 <- eval (handleImmediateWithSignExtend imm_0 8 8);
      v_5 <- getRegister xmm_2;
      v_6 <- getRegister xmm_1;
      setRegister (lhs.of_reg xmm_3) (concat (mux (isBitClear v_4 4) (extract v_5 0 32) (extract v_6 0 32)) (concat (mux (isBitClear v_4 5) (extract v_5 32 64) (extract v_6 32 64)) (concat (mux (isBitClear v_4 6) (extract v_5 64 96) (extract v_6 64 96)) (mux (isBitClear v_4 7) (extract v_5 96 128) (extract v_6 96 128)))));
      pure ()
    pat_end;
    pattern fun (imm_0 : imm int) (ymm_1 : reg (bv 256)) (ymm_2 : reg (bv 256)) (ymm_3 : reg (bv 256)) => do
      v_4 <- eval (handleImmediateWithSignExtend imm_0 8 8);
      v_5 <- getRegister ymm_2;
      v_6 <- getRegister ymm_1;
      setRegister (lhs.of_reg ymm_3) (concat (mux (isBitClear v_4 0) (extract v_5 0 32) (extract v_6 0 32)) (concat (mux (isBitClear v_4 1) (extract v_5 32 64) (extract v_6 32 64)) (concat (mux (isBitClear v_4 2) (extract v_5 64 96) (extract v_6 64 96)) (concat (mux (isBitClear v_4 3) (extract v_5 96 128) (extract v_6 96 128)) (concat (mux (isBitClear v_4 4) (extract v_5 128 160) (extract v_6 128 160)) (concat (mux (isBitClear v_4 5) (extract v_5 160 192) (extract v_6 160 192)) (concat (mux (isBitClear v_4 6) (extract v_5 192 224) (extract v_6 192 224)) (mux (isBitClear v_4 7) (extract v_5 224 256) (extract v_6 224 256)))))))));
      pure ()
    pat_end
