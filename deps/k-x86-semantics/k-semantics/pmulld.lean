def pmulld : instruction :=
  definst "pmulld" $ do
    pattern fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) => do
      v_2 <- getRegister (lhs.of_reg xmm_1);
      (v_3 : expression (bv 32)) <- eval (extract v_2 0 32);
      v_4 <- evaluateAddress mem_0;
      v_5 <- load v_4 16;
      (v_6 : expression (bv 32)) <- eval (extract v_5 0 32);
      (v_7 : expression (bv 32)) <- eval (extract (mul (sext v_3 64) (sext v_6 64)) 32 64);
      (v_8 : expression (bv 32)) <- eval (extract v_2 32 64);
      (v_9 : expression (bv 32)) <- eval (extract v_5 32 64);
      (v_10 : expression (bv 32)) <- eval (extract (mul (sext v_8 64) (sext v_9 64)) 32 64);
      (v_11 : expression (bv 32)) <- eval (extract v_2 64 96);
      (v_12 : expression (bv 32)) <- eval (extract v_5 64 96);
      (v_13 : expression (bv 32)) <- eval (extract (mul (sext v_11 64) (sext v_12 64)) 32 64);
      (v_14 : expression (bv 32)) <- eval (extract v_2 96 128);
      (v_15 : expression (bv 32)) <- eval (extract v_5 96 128);
      (v_16 : expression (bv 32)) <- eval (extract (mul (sext v_14 64) (sext v_15 64)) 32 64);
      setRegister (lhs.of_reg xmm_1) (concat v_7 (concat v_10 (concat v_13 v_16)));
      pure ()
    pat_end;
    pattern fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) => do
      v_2 <- getRegister (lhs.of_reg xmm_1);
      (v_3 : expression (bv 32)) <- eval (extract v_2 0 32);
      v_4 <- getRegister (lhs.of_reg xmm_0);
      (v_5 : expression (bv 32)) <- eval (extract v_4 0 32);
      (v_6 : expression (bv 32)) <- eval (extract (mul (sext v_3 64) (sext v_5 64)) 32 64);
      (v_7 : expression (bv 32)) <- eval (extract v_2 32 64);
      (v_8 : expression (bv 32)) <- eval (extract v_4 32 64);
      (v_9 : expression (bv 32)) <- eval (extract (mul (sext v_7 64) (sext v_8 64)) 32 64);
      (v_10 : expression (bv 32)) <- eval (extract v_2 64 96);
      (v_11 : expression (bv 32)) <- eval (extract v_4 64 96);
      (v_12 : expression (bv 32)) <- eval (extract (mul (sext v_10 64) (sext v_11 64)) 32 64);
      (v_13 : expression (bv 32)) <- eval (extract v_2 96 128);
      (v_14 : expression (bv 32)) <- eval (extract v_4 96 128);
      (v_15 : expression (bv 32)) <- eval (extract (mul (sext v_13 64) (sext v_14 64)) 32 64);
      setRegister (lhs.of_reg xmm_1) (concat v_6 (concat v_9 (concat v_12 v_15)));
      pure ()
    pat_end
