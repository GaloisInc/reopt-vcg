def vpunpcklwd : instruction :=
  definst "vpunpcklwd" $ do
    pattern fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) => do
      v_3 <- evaluateAddress mem_0;
      v_4 <- load v_3 16;
      (v_5 : expression (bv 16)) <- eval (extract v_4 64 80);
      v_6 <- getRegister (lhs.of_reg xmm_1);
      (v_7 : expression (bv 16)) <- eval (extract v_6 64 80);
      (v_8 : expression (bv 16)) <- eval (extract v_4 80 96);
      (v_9 : expression (bv 16)) <- eval (extract v_6 80 96);
      (v_10 : expression (bv 16)) <- eval (extract v_4 96 112);
      (v_11 : expression (bv 16)) <- eval (extract v_6 96 112);
      (v_12 : expression (bv 16)) <- eval (extract v_4 112 128);
      (v_13 : expression (bv 16)) <- eval (extract v_6 112 128);
      setRegister (lhs.of_reg xmm_2) (concat (concat v_5 v_7) (concat (concat v_8 v_9) (concat (concat v_10 v_11) (concat v_12 v_13))));
      pure ()
    pat_end;
    pattern fun (mem_0 : Mem) (ymm_1 : reg (bv 256)) (ymm_2 : reg (bv 256)) => do
      v_3 <- evaluateAddress mem_0;
      v_4 <- load v_3 32;
      (v_5 : expression (bv 16)) <- eval (extract v_4 64 80);
      v_6 <- getRegister (lhs.of_reg ymm_1);
      (v_7 : expression (bv 16)) <- eval (extract v_6 64 80);
      (v_8 : expression (bv 16)) <- eval (extract v_4 80 96);
      (v_9 : expression (bv 16)) <- eval (extract v_6 80 96);
      (v_10 : expression (bv 16)) <- eval (extract v_4 96 112);
      (v_11 : expression (bv 16)) <- eval (extract v_6 96 112);
      (v_12 : expression (bv 16)) <- eval (extract v_4 112 128);
      (v_13 : expression (bv 16)) <- eval (extract v_6 112 128);
      (v_14 : expression (bv 16)) <- eval (extract v_4 192 208);
      (v_15 : expression (bv 16)) <- eval (extract v_6 192 208);
      (v_16 : expression (bv 16)) <- eval (extract v_4 208 224);
      (v_17 : expression (bv 16)) <- eval (extract v_6 208 224);
      (v_18 : expression (bv 16)) <- eval (extract v_4 224 240);
      (v_19 : expression (bv 16)) <- eval (extract v_6 224 240);
      (v_20 : expression (bv 16)) <- eval (extract v_4 240 256);
      (v_21 : expression (bv 16)) <- eval (extract v_6 240 256);
      setRegister (lhs.of_reg ymm_2) (concat (concat v_5 v_7) (concat (concat v_8 v_9) (concat (concat v_10 v_11) (concat (concat v_12 v_13) (concat (concat v_14 v_15) (concat (concat v_16 v_17) (concat (concat v_18 v_19) (concat v_20 v_21))))))));
      pure ()
    pat_end;
    pattern fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) => do
      v_3 <- getRegister (lhs.of_reg xmm_0);
      (v_4 : expression (bv 16)) <- eval (extract v_3 64 80);
      v_5 <- getRegister (lhs.of_reg xmm_1);
      (v_6 : expression (bv 16)) <- eval (extract v_5 64 80);
      (v_7 : expression (bv 16)) <- eval (extract v_3 80 96);
      (v_8 : expression (bv 16)) <- eval (extract v_5 80 96);
      (v_9 : expression (bv 16)) <- eval (extract v_3 96 112);
      (v_10 : expression (bv 16)) <- eval (extract v_5 96 112);
      (v_11 : expression (bv 16)) <- eval (extract v_3 112 128);
      (v_12 : expression (bv 16)) <- eval (extract v_5 112 128);
      setRegister (lhs.of_reg xmm_2) (concat (concat v_4 v_6) (concat (concat v_7 v_8) (concat (concat v_9 v_10) (concat v_11 v_12))));
      pure ()
    pat_end;
    pattern fun (ymm_0 : reg (bv 256)) (ymm_1 : reg (bv 256)) (ymm_2 : reg (bv 256)) => do
      v_3 <- getRegister (lhs.of_reg ymm_0);
      (v_4 : expression (bv 16)) <- eval (extract v_3 64 80);
      v_5 <- getRegister (lhs.of_reg ymm_1);
      (v_6 : expression (bv 16)) <- eval (extract v_5 64 80);
      (v_7 : expression (bv 16)) <- eval (extract v_3 80 96);
      (v_8 : expression (bv 16)) <- eval (extract v_5 80 96);
      (v_9 : expression (bv 16)) <- eval (extract v_3 96 112);
      (v_10 : expression (bv 16)) <- eval (extract v_5 96 112);
      (v_11 : expression (bv 16)) <- eval (extract v_3 112 128);
      (v_12 : expression (bv 16)) <- eval (extract v_5 112 128);
      (v_13 : expression (bv 16)) <- eval (extract v_3 192 208);
      (v_14 : expression (bv 16)) <- eval (extract v_5 192 208);
      (v_15 : expression (bv 16)) <- eval (extract v_3 208 224);
      (v_16 : expression (bv 16)) <- eval (extract v_5 208 224);
      (v_17 : expression (bv 16)) <- eval (extract v_3 224 240);
      (v_18 : expression (bv 16)) <- eval (extract v_5 224 240);
      (v_19 : expression (bv 16)) <- eval (extract v_3 240 256);
      (v_20 : expression (bv 16)) <- eval (extract v_5 240 256);
      setRegister (lhs.of_reg ymm_2) (concat (concat v_4 v_6) (concat (concat v_7 v_8) (concat (concat v_9 v_10) (concat (concat v_11 v_12) (concat (concat v_13 v_14) (concat (concat v_15 v_16) (concat (concat v_17 v_18) (concat v_19 v_20))))))));
      pure ()
    pat_end
