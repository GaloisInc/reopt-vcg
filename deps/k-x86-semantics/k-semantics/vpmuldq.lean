def vpmuldq : instruction :=
  definst "vpmuldq" $ do
    pattern fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) => do
      v_3 <- getRegister (lhs.of_reg xmm_1);
      (v_4 : expression (bv 32)) <- eval (extract v_3 32 64);
      v_5 <- evaluateAddress mem_0;
      v_6 <- load v_5 16;
      (v_7 : expression (bv 32)) <- eval (extract v_6 32 64);
      (v_8 : expression (bv 32)) <- eval (extract v_3 96 128);
      (v_9 : expression (bv 32)) <- eval (extract v_6 96 128);
      setRegister (lhs.of_reg xmm_2) (concat (mul (sext v_4 64) (sext v_7 64)) (mul (sext v_8 64) (sext v_9 64)));
      pure ()
    pat_end;
    pattern fun (mem_0 : Mem) (ymm_1 : reg (bv 256)) (ymm_2 : reg (bv 256)) => do
      v_3 <- getRegister (lhs.of_reg ymm_1);
      (v_4 : expression (bv 32)) <- eval (extract v_3 32 64);
      v_5 <- evaluateAddress mem_0;
      v_6 <- load v_5 32;
      (v_7 : expression (bv 32)) <- eval (extract v_6 32 64);
      (v_8 : expression (bv 32)) <- eval (extract v_3 96 128);
      (v_9 : expression (bv 32)) <- eval (extract v_6 96 128);
      (v_10 : expression (bv 32)) <- eval (extract v_3 160 192);
      (v_11 : expression (bv 32)) <- eval (extract v_6 160 192);
      (v_12 : expression (bv 32)) <- eval (extract v_3 224 256);
      (v_13 : expression (bv 32)) <- eval (extract v_6 224 256);
      setRegister (lhs.of_reg ymm_2) (concat (mul (sext v_4 64) (sext v_7 64)) (concat (mul (sext v_8 64) (sext v_9 64)) (concat (mul (sext v_10 64) (sext v_11 64)) (mul (sext v_12 64) (sext v_13 64)))));
      pure ()
    pat_end;
    pattern fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) => do
      v_3 <- getRegister (lhs.of_reg xmm_1);
      (v_4 : expression (bv 32)) <- eval (extract v_3 32 64);
      v_5 <- getRegister (lhs.of_reg xmm_0);
      (v_6 : expression (bv 32)) <- eval (extract v_5 32 64);
      (v_7 : expression (bv 32)) <- eval (extract v_3 96 128);
      (v_8 : expression (bv 32)) <- eval (extract v_5 96 128);
      setRegister (lhs.of_reg xmm_2) (concat (mul (sext v_4 64) (sext v_6 64)) (mul (sext v_7 64) (sext v_8 64)));
      pure ()
    pat_end;
    pattern fun (ymm_0 : reg (bv 256)) (ymm_1 : reg (bv 256)) (ymm_2 : reg (bv 256)) => do
      v_3 <- getRegister (lhs.of_reg ymm_1);
      (v_4 : expression (bv 32)) <- eval (extract v_3 32 64);
      v_5 <- getRegister (lhs.of_reg ymm_0);
      (v_6 : expression (bv 32)) <- eval (extract v_5 32 64);
      (v_7 : expression (bv 32)) <- eval (extract v_3 96 128);
      (v_8 : expression (bv 32)) <- eval (extract v_5 96 128);
      (v_9 : expression (bv 32)) <- eval (extract v_3 160 192);
      (v_10 : expression (bv 32)) <- eval (extract v_5 160 192);
      (v_11 : expression (bv 32)) <- eval (extract v_3 224 256);
      (v_12 : expression (bv 32)) <- eval (extract v_5 224 256);
      setRegister (lhs.of_reg ymm_2) (concat (mul (sext v_4 64) (sext v_6 64)) (concat (mul (sext v_7 64) (sext v_8 64)) (concat (mul (sext v_9 64) (sext v_10 64)) (mul (sext v_11 64) (sext v_12 64)))));
      pure ()
    pat_end
