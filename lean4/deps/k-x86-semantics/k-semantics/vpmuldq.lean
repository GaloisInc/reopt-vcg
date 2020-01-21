def vpmuldq : instruction :=
  definst "vpmuldq" $ do
    pattern fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) => do
      v_3 <- getRegister (lhs.of_reg xmm_1);
      v_4 <- evaluateAddress mem_0;
      v_5 <- load v_4 16;
      setRegister (lhs.of_reg xmm_2) (concat (mul (sext (extract v_3 32 64) 64) (sext (extract v_5 32 64) 64)) (mul (sext (extract v_3 96 128) 64) (sext (extract v_5 96 128) 64)));
      pure ()
    pat_end;
    pattern fun (mem_0 : Mem) (ymm_1 : reg (bv 256)) (ymm_2 : reg (bv 256)) => do
      v_3 <- getRegister (lhs.of_reg ymm_1);
      v_4 <- evaluateAddress mem_0;
      v_5 <- load v_4 32;
      setRegister (lhs.of_reg ymm_2) (concat (mul (sext (extract v_3 32 64) 64) (sext (extract v_5 32 64) 64)) (concat (mul (sext (extract v_3 96 128) 64) (sext (extract v_5 96 128) 64)) (concat (mul (sext (extract v_3 160 192) 64) (sext (extract v_5 160 192) 64)) (mul (sext (extract v_3 224 256) 64) (sext (extract v_5 224 256) 64)))));
      pure ()
    pat_end;
    pattern fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) => do
      v_3 <- getRegister (lhs.of_reg xmm_1);
      v_4 <- getRegister (lhs.of_reg xmm_0);
      setRegister (lhs.of_reg xmm_2) (concat (mul (sext (extract v_3 32 64) 64) (sext (extract v_4 32 64) 64)) (mul (sext (extract v_3 96 128) 64) (sext (extract v_4 96 128) 64)));
      pure ()
    pat_end;
    pattern fun (ymm_0 : reg (bv 256)) (ymm_1 : reg (bv 256)) (ymm_2 : reg (bv 256)) => do
      v_3 <- getRegister (lhs.of_reg ymm_1);
      v_4 <- getRegister (lhs.of_reg ymm_0);
      setRegister (lhs.of_reg ymm_2) (concat (mul (sext (extract v_3 32 64) 64) (sext (extract v_4 32 64) 64)) (concat (mul (sext (extract v_3 96 128) 64) (sext (extract v_4 96 128) 64)) (concat (mul (sext (extract v_3 160 192) 64) (sext (extract v_4 160 192) 64)) (mul (sext (extract v_3 224 256) 64) (sext (extract v_4 224 256) 64)))));
      pure ()
    pat_end
