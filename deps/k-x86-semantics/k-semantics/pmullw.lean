def pmullw : instruction :=
  definst "pmullw" $ do
    pattern fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) => do
      v_2 <- getRegister (lhs.of_reg xmm_1);
      (v_3 : expression (bv 16)) <- eval (extract v_2 0 16);
      v_4 <- evaluateAddress mem_0;
      v_5 <- load v_4 16;
      (v_6 : expression (bv 16)) <- eval (extract v_5 0 16);
      (v_7 : expression (bv 16)) <- eval (extract (mul (sext v_3 32) (sext v_6 32)) 16 32);
      (v_8 : expression (bv 16)) <- eval (extract v_2 16 32);
      (v_9 : expression (bv 16)) <- eval (extract v_5 16 32);
      (v_10 : expression (bv 16)) <- eval (extract (mul (sext v_8 32) (sext v_9 32)) 16 32);
      (v_11 : expression (bv 16)) <- eval (extract v_2 32 48);
      (v_12 : expression (bv 16)) <- eval (extract v_5 32 48);
      (v_13 : expression (bv 16)) <- eval (extract (mul (sext v_11 32) (sext v_12 32)) 16 32);
      (v_14 : expression (bv 16)) <- eval (extract v_2 48 64);
      (v_15 : expression (bv 16)) <- eval (extract v_5 48 64);
      (v_16 : expression (bv 16)) <- eval (extract (mul (sext v_14 32) (sext v_15 32)) 16 32);
      (v_17 : expression (bv 16)) <- eval (extract v_2 64 80);
      (v_18 : expression (bv 16)) <- eval (extract v_5 64 80);
      (v_19 : expression (bv 16)) <- eval (extract (mul (sext v_17 32) (sext v_18 32)) 16 32);
      (v_20 : expression (bv 16)) <- eval (extract v_2 80 96);
      (v_21 : expression (bv 16)) <- eval (extract v_5 80 96);
      (v_22 : expression (bv 16)) <- eval (extract (mul (sext v_20 32) (sext v_21 32)) 16 32);
      (v_23 : expression (bv 16)) <- eval (extract v_2 96 112);
      (v_24 : expression (bv 16)) <- eval (extract v_5 96 112);
      (v_25 : expression (bv 16)) <- eval (extract (mul (sext v_23 32) (sext v_24 32)) 16 32);
      (v_26 : expression (bv 16)) <- eval (extract v_2 112 128);
      (v_27 : expression (bv 16)) <- eval (extract v_5 112 128);
      (v_28 : expression (bv 16)) <- eval (extract (mul (sext v_26 32) (sext v_27 32)) 16 32);
      setRegister (lhs.of_reg xmm_1) (concat v_7 (concat v_10 (concat v_13 (concat v_16 (concat v_19 (concat v_22 (concat v_25 v_28)))))));
      pure ()
    pat_end;
    pattern fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) => do
      v_2 <- getRegister (lhs.of_reg xmm_1);
      (v_3 : expression (bv 16)) <- eval (extract v_2 0 16);
      v_4 <- getRegister (lhs.of_reg xmm_0);
      (v_5 : expression (bv 16)) <- eval (extract v_4 0 16);
      (v_6 : expression (bv 16)) <- eval (extract (mul (sext v_3 32) (sext v_5 32)) 16 32);
      (v_7 : expression (bv 16)) <- eval (extract v_2 16 32);
      (v_8 : expression (bv 16)) <- eval (extract v_4 16 32);
      (v_9 : expression (bv 16)) <- eval (extract (mul (sext v_7 32) (sext v_8 32)) 16 32);
      (v_10 : expression (bv 16)) <- eval (extract v_2 32 48);
      (v_11 : expression (bv 16)) <- eval (extract v_4 32 48);
      (v_12 : expression (bv 16)) <- eval (extract (mul (sext v_10 32) (sext v_11 32)) 16 32);
      (v_13 : expression (bv 16)) <- eval (extract v_2 48 64);
      (v_14 : expression (bv 16)) <- eval (extract v_4 48 64);
      (v_15 : expression (bv 16)) <- eval (extract (mul (sext v_13 32) (sext v_14 32)) 16 32);
      (v_16 : expression (bv 16)) <- eval (extract v_2 64 80);
      (v_17 : expression (bv 16)) <- eval (extract v_4 64 80);
      (v_18 : expression (bv 16)) <- eval (extract (mul (sext v_16 32) (sext v_17 32)) 16 32);
      (v_19 : expression (bv 16)) <- eval (extract v_2 80 96);
      (v_20 : expression (bv 16)) <- eval (extract v_4 80 96);
      (v_21 : expression (bv 16)) <- eval (extract (mul (sext v_19 32) (sext v_20 32)) 16 32);
      (v_22 : expression (bv 16)) <- eval (extract v_2 96 112);
      (v_23 : expression (bv 16)) <- eval (extract v_4 96 112);
      (v_24 : expression (bv 16)) <- eval (extract (mul (sext v_22 32) (sext v_23 32)) 16 32);
      (v_25 : expression (bv 16)) <- eval (extract v_2 112 128);
      (v_26 : expression (bv 16)) <- eval (extract v_4 112 128);
      (v_27 : expression (bv 16)) <- eval (extract (mul (sext v_25 32) (sext v_26 32)) 16 32);
      setRegister (lhs.of_reg xmm_1) (concat v_6 (concat v_9 (concat v_12 (concat v_15 (concat v_18 (concat v_21 (concat v_24 v_27)))))));
      pure ()
    pat_end
