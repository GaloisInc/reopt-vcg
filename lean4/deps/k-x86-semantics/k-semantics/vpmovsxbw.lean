def vpmovsxbw : instruction :=
  definst "vpmovsxbw" $ do
    pattern fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) => do
      v_2 <- evaluateAddress mem_0;
      v_3 <- load v_2 8;
      (v_4 : expression (bv 8)) <- eval (extract v_3 0 8);
      (v_5 : expression (bv 8)) <- eval (extract v_3 8 16);
      (v_6 : expression (bv 8)) <- eval (extract v_3 16 24);
      (v_7 : expression (bv 8)) <- eval (extract v_3 24 32);
      (v_8 : expression (bv 8)) <- eval (extract v_3 32 40);
      (v_9 : expression (bv 8)) <- eval (extract v_3 40 48);
      (v_10 : expression (bv 8)) <- eval (extract v_3 48 56);
      (v_11 : expression (bv 8)) <- eval (extract v_3 56 64);
      setRegister (lhs.of_reg xmm_1) (concat (sext v_4 16) (concat (sext v_5 16) (concat (sext v_6 16) (concat (sext v_7 16) (concat (sext v_8 16) (concat (sext v_9 16) (concat (sext v_10 16) (sext v_11 16))))))));
      pure ()
    pat_end;
    pattern fun (mem_0 : Mem) (ymm_1 : reg (bv 256)) => do
      v_2 <- evaluateAddress mem_0;
      v_3 <- load v_2 16;
      (v_4 : expression (bv 8)) <- eval (extract v_3 0 8);
      (v_5 : expression (bv 8)) <- eval (extract v_3 8 16);
      (v_6 : expression (bv 8)) <- eval (extract v_3 16 24);
      (v_7 : expression (bv 8)) <- eval (extract v_3 24 32);
      (v_8 : expression (bv 8)) <- eval (extract v_3 32 40);
      (v_9 : expression (bv 8)) <- eval (extract v_3 40 48);
      (v_10 : expression (bv 8)) <- eval (extract v_3 48 56);
      (v_11 : expression (bv 8)) <- eval (extract v_3 56 64);
      (v_12 : expression (bv 8)) <- eval (extract v_3 64 72);
      (v_13 : expression (bv 8)) <- eval (extract v_3 72 80);
      (v_14 : expression (bv 8)) <- eval (extract v_3 80 88);
      (v_15 : expression (bv 8)) <- eval (extract v_3 88 96);
      (v_16 : expression (bv 8)) <- eval (extract v_3 96 104);
      (v_17 : expression (bv 8)) <- eval (extract v_3 104 112);
      (v_18 : expression (bv 8)) <- eval (extract v_3 112 120);
      (v_19 : expression (bv 8)) <- eval (extract v_3 120 128);
      setRegister (lhs.of_reg ymm_1) (concat (sext v_4 16) (concat (sext v_5 16) (concat (sext v_6 16) (concat (sext v_7 16) (concat (sext v_8 16) (concat (sext v_9 16) (concat (sext v_10 16) (concat (sext v_11 16) (concat (sext v_12 16) (concat (sext v_13 16) (concat (sext v_14 16) (concat (sext v_15 16) (concat (sext v_16 16) (concat (sext v_17 16) (concat (sext v_18 16) (sext v_19 16))))))))))))))));
      pure ()
    pat_end;
    pattern fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) => do
      v_2 <- getRegister (lhs.of_reg xmm_0);
      (v_3 : expression (bv 8)) <- eval (extract v_2 64 72);
      (v_4 : expression (bv 8)) <- eval (extract v_2 72 80);
      (v_5 : expression (bv 8)) <- eval (extract v_2 80 88);
      (v_6 : expression (bv 8)) <- eval (extract v_2 88 96);
      (v_7 : expression (bv 8)) <- eval (extract v_2 96 104);
      (v_8 : expression (bv 8)) <- eval (extract v_2 104 112);
      (v_9 : expression (bv 8)) <- eval (extract v_2 112 120);
      (v_10 : expression (bv 8)) <- eval (extract v_2 120 128);
      setRegister (lhs.of_reg xmm_1) (concat (sext v_3 16) (concat (sext v_4 16) (concat (sext v_5 16) (concat (sext v_6 16) (concat (sext v_7 16) (concat (sext v_8 16) (concat (sext v_9 16) (sext v_10 16))))))));
      pure ()
    pat_end;
    pattern fun (xmm_0 : reg (bv 128)) (ymm_1 : reg (bv 256)) => do
      v_2 <- getRegister (lhs.of_reg xmm_0);
      (v_3 : expression (bv 8)) <- eval (extract v_2 0 8);
      (v_4 : expression (bv 8)) <- eval (extract v_2 8 16);
      (v_5 : expression (bv 8)) <- eval (extract v_2 16 24);
      (v_6 : expression (bv 8)) <- eval (extract v_2 24 32);
      (v_7 : expression (bv 8)) <- eval (extract v_2 32 40);
      (v_8 : expression (bv 8)) <- eval (extract v_2 40 48);
      (v_9 : expression (bv 8)) <- eval (extract v_2 48 56);
      (v_10 : expression (bv 8)) <- eval (extract v_2 56 64);
      (v_11 : expression (bv 8)) <- eval (extract v_2 64 72);
      (v_12 : expression (bv 8)) <- eval (extract v_2 72 80);
      (v_13 : expression (bv 8)) <- eval (extract v_2 80 88);
      (v_14 : expression (bv 8)) <- eval (extract v_2 88 96);
      (v_15 : expression (bv 8)) <- eval (extract v_2 96 104);
      (v_16 : expression (bv 8)) <- eval (extract v_2 104 112);
      (v_17 : expression (bv 8)) <- eval (extract v_2 112 120);
      (v_18 : expression (bv 8)) <- eval (extract v_2 120 128);
      setRegister (lhs.of_reg ymm_1) (concat (sext v_3 16) (concat (sext v_4 16) (concat (sext v_5 16) (concat (sext v_6 16) (concat (sext v_7 16) (concat (sext v_8 16) (concat (sext v_9 16) (concat (sext v_10 16) (concat (sext v_11 16) (concat (sext v_12 16) (concat (sext v_13 16) (concat (sext v_14 16) (concat (sext v_15 16) (concat (sext v_16 16) (concat (sext v_17 16) (sext v_18 16))))))))))))))));
      pure ()
    pat_end