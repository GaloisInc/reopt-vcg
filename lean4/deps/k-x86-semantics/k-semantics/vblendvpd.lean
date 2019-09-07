def vblendvpd1 : instruction :=
  definst "vblendvpd" $ do
    pattern fun (xmm_0 : reg (bv 128)) (mem_1 : Mem) (xmm_2 : reg (bv 128)) (xmm_3 : reg (bv 128)) => do
      v_4 <- getRegister xmm_0;
      v_5 <- getRegister xmm_2;
      v_6 <- evaluateAddress mem_1;
      v_7 <- load v_6 16;
      setRegister (lhs.of_reg xmm_3) (concat (mux (isBitClear v_4 0) (extract v_5 0 64) (extract v_7 0 64)) (mux (isBitClear v_4 64) (extract v_5 64 128) (extract v_7 64 128)));
      pure ()
    pat_end;
    pattern fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) (xmm_3 : reg (bv 128)) => do
      v_4 <- getRegister xmm_0;
      v_5 <- getRegister xmm_2;
      v_6 <- getRegister xmm_1;
      setRegister (lhs.of_reg xmm_3) (concat (mux (isBitClear v_4 0) (extract v_5 0 64) (extract v_6 0 64)) (mux (isBitClear v_4 64) (extract v_5 64 128) (extract v_6 64 128)));
      pure ()
    pat_end;
    pattern fun (ymm_0 : reg (bv 256)) (mem_1 : Mem) (ymm_2 : reg (bv 256)) (ymm_3 : reg (bv 256)) => do
      v_4 <- getRegister ymm_0;
      v_5 <- getRegister ymm_2;
      v_6 <- evaluateAddress mem_1;
      v_7 <- load v_6 32;
      setRegister (lhs.of_reg ymm_3) (concat (mux (isBitClear v_4 0) (extract v_5 0 64) (extract v_7 0 64)) (concat (mux (isBitClear v_4 64) (extract v_5 64 128) (extract v_7 64 128)) (concat (mux (isBitClear v_4 128) (extract v_5 128 192) (extract v_7 128 192)) (mux (isBitClear v_4 192) (extract v_5 192 256) (extract v_7 192 256)))));
      pure ()
    pat_end;
    pattern fun (ymm_0 : reg (bv 256)) (ymm_1 : reg (bv 256)) (ymm_2 : reg (bv 256)) (ymm_3 : reg (bv 256)) => do
      v_4 <- getRegister ymm_0;
      v_5 <- getRegister ymm_2;
      v_6 <- getRegister ymm_1;
      setRegister (lhs.of_reg ymm_3) (concat (mux (isBitClear v_4 0) (extract v_5 0 64) (extract v_6 0 64)) (concat (mux (isBitClear v_4 64) (extract v_5 64 128) (extract v_6 64 128)) (concat (mux (isBitClear v_4 128) (extract v_5 128 192) (extract v_6 128 192)) (mux (isBitClear v_4 192) (extract v_5 192 256) (extract v_6 192 256)))));
      pure ()
    pat_end
