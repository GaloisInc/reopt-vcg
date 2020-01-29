def vpmulld : instruction :=
  definst "vpmulld" $ do
    pattern fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) => do
      v_3 <- getRegister (lhs.of_reg xmm_1);
      (v_4 : expression (bv 32)) <- eval (extract v_3 0 32);
      v_5 <- evaluateAddress mem_0;
      v_6 <- load v_5 16;
      (v_7 : expression (bv 32)) <- eval (extract v_6 0 32);
      (v_8 : expression (bv 32)) <- eval (extract (mul (sext v_4 64) (sext v_7 64)) 32 64);
      (v_9 : expression (bv 32)) <- eval (extract v_3 32 64);
      (v_10 : expression (bv 32)) <- eval (extract v_6 32 64);
      (v_11 : expression (bv 32)) <- eval (extract (mul (sext v_9 64) (sext v_10 64)) 32 64);
      (v_12 : expression (bv 32)) <- eval (extract v_3 64 96);
      (v_13 : expression (bv 32)) <- eval (extract v_6 64 96);
      (v_14 : expression (bv 32)) <- eval (extract (mul (sext v_12 64) (sext v_13 64)) 32 64);
      (v_15 : expression (bv 32)) <- eval (extract v_3 96 128);
      (v_16 : expression (bv 32)) <- eval (extract v_6 96 128);
      (v_17 : expression (bv 32)) <- eval (extract (mul (sext v_15 64) (sext v_16 64)) 32 64);
      setRegister (lhs.of_reg xmm_2) (concat v_8 (concat v_11 (concat v_14 v_17)));
      pure ()
    pat_end;
    pattern fun (mem_0 : Mem) (ymm_1 : reg (bv 256)) (ymm_2 : reg (bv 256)) => do
      v_3 <- getRegister (lhs.of_reg ymm_1);
      (v_4 : expression (bv 32)) <- eval (extract v_3 0 32);
      v_5 <- evaluateAddress mem_0;
      v_6 <- load v_5 32;
      (v_7 : expression (bv 32)) <- eval (extract v_6 0 32);
      (v_8 : expression (bv 32)) <- eval (extract (mul (sext v_4 64) (sext v_7 64)) 32 64);
      (v_9 : expression (bv 32)) <- eval (extract v_3 32 64);
      (v_10 : expression (bv 32)) <- eval (extract v_6 32 64);
      (v_11 : expression (bv 32)) <- eval (extract (mul (sext v_9 64) (sext v_10 64)) 32 64);
      (v_12 : expression (bv 32)) <- eval (extract v_3 64 96);
      (v_13 : expression (bv 32)) <- eval (extract v_6 64 96);
      (v_14 : expression (bv 32)) <- eval (extract (mul (sext v_12 64) (sext v_13 64)) 32 64);
      (v_15 : expression (bv 32)) <- eval (extract v_3 96 128);
      (v_16 : expression (bv 32)) <- eval (extract v_6 96 128);
      (v_17 : expression (bv 32)) <- eval (extract (mul (sext v_15 64) (sext v_16 64)) 32 64);
      (v_18 : expression (bv 32)) <- eval (extract v_3 128 160);
      (v_19 : expression (bv 32)) <- eval (extract v_6 128 160);
      (v_20 : expression (bv 32)) <- eval (extract (mul (sext v_18 64) (sext v_19 64)) 32 64);
      (v_21 : expression (bv 32)) <- eval (extract v_3 160 192);
      (v_22 : expression (bv 32)) <- eval (extract v_6 160 192);
      (v_23 : expression (bv 32)) <- eval (extract (mul (sext v_21 64) (sext v_22 64)) 32 64);
      (v_24 : expression (bv 32)) <- eval (extract v_3 192 224);
      (v_25 : expression (bv 32)) <- eval (extract v_6 192 224);
      (v_26 : expression (bv 32)) <- eval (extract (mul (sext v_24 64) (sext v_25 64)) 32 64);
      (v_27 : expression (bv 32)) <- eval (extract v_3 224 256);
      (v_28 : expression (bv 32)) <- eval (extract v_6 224 256);
      (v_29 : expression (bv 32)) <- eval (extract (mul (sext v_27 64) (sext v_28 64)) 32 64);
      setRegister (lhs.of_reg ymm_2) (concat v_8 (concat v_11 (concat v_14 (concat v_17 (concat v_20 (concat v_23 (concat v_26 v_29)))))));
      pure ()
    pat_end;
    pattern fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) => do
      v_3 <- getRegister (lhs.of_reg xmm_1);
      (v_4 : expression (bv 32)) <- eval (extract v_3 0 32);
      v_5 <- getRegister (lhs.of_reg xmm_0);
      (v_6 : expression (bv 32)) <- eval (extract v_5 0 32);
      (v_7 : expression (bv 32)) <- eval (extract (mul (sext v_4 64) (sext v_6 64)) 32 64);
      (v_8 : expression (bv 32)) <- eval (extract v_3 32 64);
      (v_9 : expression (bv 32)) <- eval (extract v_5 32 64);
      (v_10 : expression (bv 32)) <- eval (extract (mul (sext v_8 64) (sext v_9 64)) 32 64);
      (v_11 : expression (bv 32)) <- eval (extract v_3 64 96);
      (v_12 : expression (bv 32)) <- eval (extract v_5 64 96);
      (v_13 : expression (bv 32)) <- eval (extract (mul (sext v_11 64) (sext v_12 64)) 32 64);
      (v_14 : expression (bv 32)) <- eval (extract v_3 96 128);
      (v_15 : expression (bv 32)) <- eval (extract v_5 96 128);
      (v_16 : expression (bv 32)) <- eval (extract (mul (sext v_14 64) (sext v_15 64)) 32 64);
      setRegister (lhs.of_reg xmm_2) (concat v_7 (concat v_10 (concat v_13 v_16)));
      pure ()
    pat_end;
    pattern fun (ymm_0 : reg (bv 256)) (ymm_1 : reg (bv 256)) (ymm_2 : reg (bv 256)) => do
      v_3 <- getRegister (lhs.of_reg ymm_1);
      (v_4 : expression (bv 32)) <- eval (extract v_3 0 32);
      v_5 <- getRegister (lhs.of_reg ymm_0);
      (v_6 : expression (bv 32)) <- eval (extract v_5 0 32);
      (v_7 : expression (bv 32)) <- eval (extract (mul (sext v_4 64) (sext v_6 64)) 32 64);
      (v_8 : expression (bv 32)) <- eval (extract v_3 32 64);
      (v_9 : expression (bv 32)) <- eval (extract v_5 32 64);
      (v_10 : expression (bv 32)) <- eval (extract (mul (sext v_8 64) (sext v_9 64)) 32 64);
      (v_11 : expression (bv 32)) <- eval (extract v_3 64 96);
      (v_12 : expression (bv 32)) <- eval (extract v_5 64 96);
      (v_13 : expression (bv 32)) <- eval (extract (mul (sext v_11 64) (sext v_12 64)) 32 64);
      (v_14 : expression (bv 32)) <- eval (extract v_3 96 128);
      (v_15 : expression (bv 32)) <- eval (extract v_5 96 128);
      (v_16 : expression (bv 32)) <- eval (extract (mul (sext v_14 64) (sext v_15 64)) 32 64);
      (v_17 : expression (bv 32)) <- eval (extract v_3 128 160);
      (v_18 : expression (bv 32)) <- eval (extract v_5 128 160);
      (v_19 : expression (bv 32)) <- eval (extract (mul (sext v_17 64) (sext v_18 64)) 32 64);
      (v_20 : expression (bv 32)) <- eval (extract v_3 160 192);
      (v_21 : expression (bv 32)) <- eval (extract v_5 160 192);
      (v_22 : expression (bv 32)) <- eval (extract (mul (sext v_20 64) (sext v_21 64)) 32 64);
      (v_23 : expression (bv 32)) <- eval (extract v_3 192 224);
      (v_24 : expression (bv 32)) <- eval (extract v_5 192 224);
      (v_25 : expression (bv 32)) <- eval (extract (mul (sext v_23 64) (sext v_24 64)) 32 64);
      (v_26 : expression (bv 32)) <- eval (extract v_3 224 256);
      (v_27 : expression (bv 32)) <- eval (extract v_5 224 256);
      (v_28 : expression (bv 32)) <- eval (extract (mul (sext v_26 64) (sext v_27 64)) 32 64);
      setRegister (lhs.of_reg ymm_2) (concat v_7 (concat v_10 (concat v_13 (concat v_16 (concat v_19 (concat v_22 (concat v_25 v_28)))))));
      pure ()
    pat_end
