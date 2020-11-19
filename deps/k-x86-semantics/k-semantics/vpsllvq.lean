def vpsllvq : instruction :=
  definst "vpsllvq" $ do
    pattern fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) => do
      v_3 <- getRegister (lhs.of_reg xmm_1);
      (v_4 : expression (bv 64)) <- eval (extract v_3 0 64);
      v_5 <- evaluateAddress mem_0;
      v_6 <- load v_5 16;
      (v_7 : expression (bv 64)) <- eval (extract v_6 0 64);
      (v_8 : expression (bv 64)) <- eval (extract (shl v_4 v_7) 0 64);
      (v_9 : expression (bv 64)) <- eval (extract v_3 64 128);
      (v_10 : expression (bv 64)) <- eval (extract v_6 64 128);
      (v_11 : expression (bv 64)) <- eval (extract (shl v_9 v_10) 0 64);
      setRegister (lhs.of_reg xmm_2) (concat v_8 v_11);
      pure ()
    pat_end;
    pattern fun (mem_0 : Mem) (ymm_1 : reg (bv 256)) (ymm_2 : reg (bv 256)) => do
      v_3 <- getRegister (lhs.of_reg ymm_1);
      (v_4 : expression (bv 64)) <- eval (extract v_3 0 64);
      v_5 <- evaluateAddress mem_0;
      v_6 <- load v_5 32;
      (v_7 : expression (bv 64)) <- eval (extract v_6 0 64);
      (v_8 : expression (bv 64)) <- eval (extract (shl v_4 v_7) 0 64);
      (v_9 : expression (bv 64)) <- eval (extract v_3 64 128);
      (v_10 : expression (bv 64)) <- eval (extract v_6 64 128);
      (v_11 : expression (bv 64)) <- eval (extract (shl v_9 v_10) 0 64);
      (v_12 : expression (bv 64)) <- eval (extract v_3 128 192);
      (v_13 : expression (bv 64)) <- eval (extract v_6 128 192);
      (v_14 : expression (bv 64)) <- eval (extract (shl v_12 v_13) 0 64);
      (v_15 : expression (bv 64)) <- eval (extract v_3 192 256);
      (v_16 : expression (bv 64)) <- eval (extract v_6 192 256);
      (v_17 : expression (bv 64)) <- eval (extract (shl v_15 v_16) 0 64);
      setRegister (lhs.of_reg ymm_2) (concat v_8 (concat v_11 (concat v_14 v_17)));
      pure ()
    pat_end;
    pattern fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) => do
      v_3 <- getRegister (lhs.of_reg xmm_1);
      (v_4 : expression (bv 64)) <- eval (extract v_3 0 64);
      v_5 <- getRegister (lhs.of_reg xmm_0);
      (v_6 : expression (bv 64)) <- eval (extract v_5 0 64);
      (v_7 : expression (bv 64)) <- eval (extract (shl v_4 v_6) 0 64);
      (v_8 : expression (bv 64)) <- eval (extract v_3 64 128);
      (v_9 : expression (bv 64)) <- eval (extract v_5 64 128);
      (v_10 : expression (bv 64)) <- eval (extract (shl v_8 v_9) 0 64);
      setRegister (lhs.of_reg xmm_2) (concat v_7 v_10);
      pure ()
    pat_end;
    pattern fun (ymm_0 : reg (bv 256)) (ymm_1 : reg (bv 256)) (ymm_2 : reg (bv 256)) => do
      v_3 <- getRegister (lhs.of_reg ymm_1);
      (v_4 : expression (bv 64)) <- eval (extract v_3 0 64);
      v_5 <- getRegister (lhs.of_reg ymm_0);
      (v_6 : expression (bv 64)) <- eval (extract v_5 0 64);
      (v_7 : expression (bv 64)) <- eval (extract (shl v_4 v_6) 0 64);
      (v_8 : expression (bv 64)) <- eval (extract v_3 64 128);
      (v_9 : expression (bv 64)) <- eval (extract v_5 64 128);
      (v_10 : expression (bv 64)) <- eval (extract (shl v_8 v_9) 0 64);
      (v_11 : expression (bv 64)) <- eval (extract v_3 128 192);
      (v_12 : expression (bv 64)) <- eval (extract v_5 128 192);
      (v_13 : expression (bv 64)) <- eval (extract (shl v_11 v_12) 0 64);
      (v_14 : expression (bv 64)) <- eval (extract v_3 192 256);
      (v_15 : expression (bv 64)) <- eval (extract v_5 192 256);
      (v_16 : expression (bv 64)) <- eval (extract (shl v_14 v_15) 0 64);
      setRegister (lhs.of_reg ymm_2) (concat v_7 (concat v_10 (concat v_13 v_16)));
      pure ()
    pat_end
