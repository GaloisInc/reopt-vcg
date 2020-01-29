def pmaddwd : instruction :=
  definst "pmaddwd" $ do
    pattern fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) => do
      v_2 <- evaluateAddress mem_0;
      v_3 <- load v_2 16;
      (v_4 : expression (bv 16)) <- eval (extract v_3 16 32);
      v_5 <- getRegister (lhs.of_reg xmm_1);
      (v_6 : expression (bv 16)) <- eval (extract v_5 16 32);
      (v_7 : expression (bv 16)) <- eval (extract v_3 0 16);
      (v_8 : expression (bv 16)) <- eval (extract v_5 0 16);
      (v_9 : expression (bv 16)) <- eval (extract v_3 48 64);
      (v_10 : expression (bv 16)) <- eval (extract v_5 48 64);
      (v_11 : expression (bv 16)) <- eval (extract v_3 32 48);
      (v_12 : expression (bv 16)) <- eval (extract v_5 32 48);
      (v_13 : expression (bv 16)) <- eval (extract v_3 80 96);
      (v_14 : expression (bv 16)) <- eval (extract v_5 80 96);
      (v_15 : expression (bv 16)) <- eval (extract v_3 64 80);
      (v_16 : expression (bv 16)) <- eval (extract v_5 64 80);
      (v_17 : expression (bv 16)) <- eval (extract v_3 112 128);
      (v_18 : expression (bv 16)) <- eval (extract v_5 112 128);
      (v_19 : expression (bv 16)) <- eval (extract v_3 96 112);
      (v_20 : expression (bv 16)) <- eval (extract v_5 96 112);
      setRegister (lhs.of_reg xmm_1) (concat (add (mul (sext v_4 32) (sext v_6 32)) (mul (sext v_7 32) (sext v_8 32))) (concat (add (mul (sext v_9 32) (sext v_10 32)) (mul (sext v_11 32) (sext v_12 32))) (concat (add (mul (sext v_13 32) (sext v_14 32)) (mul (sext v_15 32) (sext v_16 32))) (add (mul (sext v_17 32) (sext v_18 32)) (mul (sext v_19 32) (sext v_20 32))))));
      pure ()
    pat_end;
    pattern fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) => do
      v_2 <- getRegister (lhs.of_reg xmm_0);
      (v_3 : expression (bv 16)) <- eval (extract v_2 16 32);
      v_4 <- getRegister (lhs.of_reg xmm_1);
      (v_5 : expression (bv 16)) <- eval (extract v_4 16 32);
      (v_6 : expression (bv 16)) <- eval (extract v_2 0 16);
      (v_7 : expression (bv 16)) <- eval (extract v_4 0 16);
      (v_8 : expression (bv 16)) <- eval (extract v_2 48 64);
      (v_9 : expression (bv 16)) <- eval (extract v_4 48 64);
      (v_10 : expression (bv 16)) <- eval (extract v_2 32 48);
      (v_11 : expression (bv 16)) <- eval (extract v_4 32 48);
      (v_12 : expression (bv 16)) <- eval (extract v_2 80 96);
      (v_13 : expression (bv 16)) <- eval (extract v_4 80 96);
      (v_14 : expression (bv 16)) <- eval (extract v_2 64 80);
      (v_15 : expression (bv 16)) <- eval (extract v_4 64 80);
      (v_16 : expression (bv 16)) <- eval (extract v_2 112 128);
      (v_17 : expression (bv 16)) <- eval (extract v_4 112 128);
      (v_18 : expression (bv 16)) <- eval (extract v_2 96 112);
      (v_19 : expression (bv 16)) <- eval (extract v_4 96 112);
      setRegister (lhs.of_reg xmm_1) (concat (add (mul (sext v_3 32) (sext v_5 32)) (mul (sext v_6 32) (sext v_7 32))) (concat (add (mul (sext v_8 32) (sext v_9 32)) (mul (sext v_10 32) (sext v_11 32))) (concat (add (mul (sext v_12 32) (sext v_13 32)) (mul (sext v_14 32) (sext v_15 32))) (add (mul (sext v_16 32) (sext v_17 32)) (mul (sext v_18 32) (sext v_19 32))))));
      pure ()
    pat_end
