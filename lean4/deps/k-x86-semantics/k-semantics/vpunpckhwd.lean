def vpunpckhwd : instruction :=
  definst "vpunpckhwd" $ do
    pattern fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) => do
      v_3 <- evaluateAddress mem_0;
      v_4 <- load v_3 16;
      (v_5 : expression (bv 16)) <- eval (extract v_4 0 16);
      v_6 <- getRegister (lhs.of_reg xmm_1);
      (v_7 : expression (bv 16)) <- eval (extract v_6 0 16);
      (v_8 : expression (bv 16)) <- eval (extract v_4 16 32);
      (v_9 : expression (bv 16)) <- eval (extract v_6 16 32);
      (v_10 : expression (bv 16)) <- eval (extract v_4 32 48);
      (v_11 : expression (bv 16)) <- eval (extract v_6 32 48);
      (v_12 : expression (bv 16)) <- eval (extract v_4 48 64);
      (v_13 : expression (bv 16)) <- eval (extract v_6 48 64);
      setRegister (lhs.of_reg xmm_2) (concat (concat v_5 v_7) (concat (concat v_8 v_9) (concat (concat v_10 v_11) (concat v_12 v_13))));
      pure ()
    pat_end;
    pattern fun (mem_0 : Mem) (ymm_1 : reg (bv 256)) (ymm_2 : reg (bv 256)) => do
      v_3 <- evaluateAddress mem_0;
      v_4 <- load v_3 32;
      (v_5 : expression (bv 16)) <- eval (extract v_4 0 16);
      v_6 <- getRegister (lhs.of_reg ymm_1);
      (v_7 : expression (bv 16)) <- eval (extract v_6 0 16);
      (v_8 : expression (bv 16)) <- eval (extract v_4 16 32);
      (v_9 : expression (bv 16)) <- eval (extract v_6 16 32);
      (v_10 : expression (bv 16)) <- eval (extract v_4 32 48);
      (v_11 : expression (bv 16)) <- eval (extract v_6 32 48);
      (v_12 : expression (bv 16)) <- eval (extract v_4 48 64);
      (v_13 : expression (bv 16)) <- eval (extract v_6 48 64);
      (v_14 : expression (bv 16)) <- eval (extract v_4 128 144);
      (v_15 : expression (bv 16)) <- eval (extract v_6 128 144);
      (v_16 : expression (bv 16)) <- eval (extract v_4 144 160);
      (v_17 : expression (bv 16)) <- eval (extract v_6 144 160);
      (v_18 : expression (bv 16)) <- eval (extract v_4 160 176);
      (v_19 : expression (bv 16)) <- eval (extract v_6 160 176);
      (v_20 : expression (bv 16)) <- eval (extract v_4 176 192);
      (v_21 : expression (bv 16)) <- eval (extract v_6 176 192);
      setRegister (lhs.of_reg ymm_2) (concat (concat v_5 v_7) (concat (concat v_8 v_9) (concat (concat v_10 v_11) (concat (concat v_12 v_13) (concat (concat v_14 v_15) (concat (concat v_16 v_17) (concat (concat v_18 v_19) (concat v_20 v_21))))))));
      pure ()
    pat_end;
    pattern fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) => do
      v_3 <- getRegister (lhs.of_reg xmm_0);
      (v_4 : expression (bv 16)) <- eval (extract v_3 0 16);
      v_5 <- getRegister (lhs.of_reg xmm_1);
      (v_6 : expression (bv 16)) <- eval (extract v_5 0 16);
      (v_7 : expression (bv 16)) <- eval (extract v_3 16 32);
      (v_8 : expression (bv 16)) <- eval (extract v_5 16 32);
      (v_9 : expression (bv 16)) <- eval (extract v_3 32 48);
      (v_10 : expression (bv 16)) <- eval (extract v_5 32 48);
      (v_11 : expression (bv 16)) <- eval (extract v_3 48 64);
      (v_12 : expression (bv 16)) <- eval (extract v_5 48 64);
      setRegister (lhs.of_reg xmm_2) (concat (concat v_4 v_6) (concat (concat v_7 v_8) (concat (concat v_9 v_10) (concat v_11 v_12))));
      pure ()
    pat_end;
    pattern fun (ymm_0 : reg (bv 256)) (ymm_1 : reg (bv 256)) (ymm_2 : reg (bv 256)) => do
      v_3 <- getRegister (lhs.of_reg ymm_0);
      (v_4 : expression (bv 16)) <- eval (extract v_3 0 16);
      v_5 <- getRegister (lhs.of_reg ymm_1);
      (v_6 : expression (bv 16)) <- eval (extract v_5 0 16);
      (v_7 : expression (bv 16)) <- eval (extract v_3 16 32);
      (v_8 : expression (bv 16)) <- eval (extract v_5 16 32);
      (v_9 : expression (bv 16)) <- eval (extract v_3 32 48);
      (v_10 : expression (bv 16)) <- eval (extract v_5 32 48);
      (v_11 : expression (bv 16)) <- eval (extract v_3 48 64);
      (v_12 : expression (bv 16)) <- eval (extract v_5 48 64);
      (v_13 : expression (bv 16)) <- eval (extract v_3 128 144);
      (v_14 : expression (bv 16)) <- eval (extract v_5 128 144);
      (v_15 : expression (bv 16)) <- eval (extract v_3 144 160);
      (v_16 : expression (bv 16)) <- eval (extract v_5 144 160);
      (v_17 : expression (bv 16)) <- eval (extract v_3 160 176);
      (v_18 : expression (bv 16)) <- eval (extract v_5 160 176);
      (v_19 : expression (bv 16)) <- eval (extract v_3 176 192);
      (v_20 : expression (bv 16)) <- eval (extract v_5 176 192);
      setRegister (lhs.of_reg ymm_2) (concat (concat v_4 v_6) (concat (concat v_7 v_8) (concat (concat v_9 v_10) (concat (concat v_11 v_12) (concat (concat v_13 v_14) (concat (concat v_15 v_16) (concat (concat v_17 v_18) (concat v_19 v_20))))))));
      pure ()
    pat_end
