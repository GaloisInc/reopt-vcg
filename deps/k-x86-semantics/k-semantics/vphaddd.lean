def vphaddd : instruction :=
  definst "vphaddd" $ do
    pattern fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) => do
      v_3 <- evaluateAddress mem_0;
      v_4 <- load v_3 16;
      (v_5 : expression (bv 32)) <- eval (extract v_4 0 32);
      (v_6 : expression (bv 32)) <- eval (extract v_4 32 64);
      (v_7 : expression (bv 32)) <- eval (extract v_4 64 96);
      (v_8 : expression (bv 32)) <- eval (extract v_4 96 128);
      v_9 <- getRegister (lhs.of_reg xmm_1);
      (v_10 : expression (bv 32)) <- eval (extract v_9 0 32);
      (v_11 : expression (bv 32)) <- eval (extract v_9 32 64);
      (v_12 : expression (bv 32)) <- eval (extract v_9 64 96);
      (v_13 : expression (bv 32)) <- eval (extract v_9 96 128);
      setRegister (lhs.of_reg xmm_2) (concat (concat (concat (add v_5 v_6) (add v_7 v_8)) (add v_10 v_11)) (add v_12 v_13));
      pure ()
    pat_end;
    pattern fun (mem_0 : Mem) (ymm_1 : reg (bv 256)) (ymm_2 : reg (bv 256)) => do
      v_3 <- evaluateAddress mem_0;
      v_4 <- load v_3 32;
      (v_5 : expression (bv 32)) <- eval (extract v_4 0 32);
      (v_6 : expression (bv 32)) <- eval (extract v_4 32 64);
      (v_7 : expression (bv 32)) <- eval (extract v_4 64 96);
      (v_8 : expression (bv 32)) <- eval (extract v_4 96 128);
      v_9 <- getRegister (lhs.of_reg ymm_1);
      (v_10 : expression (bv 32)) <- eval (extract v_9 0 32);
      (v_11 : expression (bv 32)) <- eval (extract v_9 32 64);
      (v_12 : expression (bv 32)) <- eval (extract v_9 64 96);
      (v_13 : expression (bv 32)) <- eval (extract v_9 96 128);
      (v_14 : expression (bv 32)) <- eval (extract v_4 128 160);
      (v_15 : expression (bv 32)) <- eval (extract v_4 160 192);
      (v_16 : expression (bv 32)) <- eval (extract v_4 192 224);
      (v_17 : expression (bv 32)) <- eval (extract v_4 224 256);
      (v_18 : expression (bv 32)) <- eval (extract v_9 128 160);
      (v_19 : expression (bv 32)) <- eval (extract v_9 160 192);
      (v_20 : expression (bv 32)) <- eval (extract v_9 192 224);
      (v_21 : expression (bv 32)) <- eval (extract v_9 224 256);
      setRegister (lhs.of_reg ymm_2) (concat (concat (concat (concat (add v_5 v_6) (add v_7 v_8)) (add v_10 v_11)) (add v_12 v_13)) (concat (concat (concat (add v_14 v_15) (add v_16 v_17)) (add v_18 v_19)) (add v_20 v_21)));
      pure ()
    pat_end;
    pattern fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) => do
      v_3 <- getRegister (lhs.of_reg xmm_0);
      (v_4 : expression (bv 32)) <- eval (extract v_3 0 32);
      (v_5 : expression (bv 32)) <- eval (extract v_3 32 64);
      (v_6 : expression (bv 32)) <- eval (extract v_3 64 96);
      (v_7 : expression (bv 32)) <- eval (extract v_3 96 128);
      v_8 <- getRegister (lhs.of_reg xmm_1);
      (v_9 : expression (bv 32)) <- eval (extract v_8 0 32);
      (v_10 : expression (bv 32)) <- eval (extract v_8 32 64);
      (v_11 : expression (bv 32)) <- eval (extract v_8 64 96);
      (v_12 : expression (bv 32)) <- eval (extract v_8 96 128);
      setRegister (lhs.of_reg xmm_2) (concat (concat (concat (add v_4 v_5) (add v_6 v_7)) (add v_9 v_10)) (add v_11 v_12));
      pure ()
    pat_end;
    pattern fun (ymm_0 : reg (bv 256)) (ymm_1 : reg (bv 256)) (ymm_2 : reg (bv 256)) => do
      v_3 <- getRegister (lhs.of_reg ymm_0);
      (v_4 : expression (bv 32)) <- eval (extract v_3 0 32);
      (v_5 : expression (bv 32)) <- eval (extract v_3 32 64);
      (v_6 : expression (bv 32)) <- eval (extract v_3 64 96);
      (v_7 : expression (bv 32)) <- eval (extract v_3 96 128);
      v_8 <- getRegister (lhs.of_reg ymm_1);
      (v_9 : expression (bv 32)) <- eval (extract v_8 0 32);
      (v_10 : expression (bv 32)) <- eval (extract v_8 32 64);
      (v_11 : expression (bv 32)) <- eval (extract v_8 64 96);
      (v_12 : expression (bv 32)) <- eval (extract v_8 96 128);
      (v_13 : expression (bv 32)) <- eval (extract v_3 128 160);
      (v_14 : expression (bv 32)) <- eval (extract v_3 160 192);
      (v_15 : expression (bv 32)) <- eval (extract v_3 192 224);
      (v_16 : expression (bv 32)) <- eval (extract v_3 224 256);
      (v_17 : expression (bv 32)) <- eval (extract v_8 128 160);
      (v_18 : expression (bv 32)) <- eval (extract v_8 160 192);
      (v_19 : expression (bv 32)) <- eval (extract v_8 192 224);
      (v_20 : expression (bv 32)) <- eval (extract v_8 224 256);
      setRegister (lhs.of_reg ymm_2) (concat (concat (concat (concat (add v_4 v_5) (add v_6 v_7)) (add v_9 v_10)) (add v_11 v_12)) (concat (concat (concat (add v_13 v_14) (add v_15 v_16)) (add v_17 v_18)) (add v_19 v_20)));
      pure ()
    pat_end
