def punpckhbw : instruction :=
  definst "punpckhbw" $ do
    pattern fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) => do
      v_2 <- evaluateAddress mem_0;
      v_3 <- load v_2 16;
      (v_4 : expression (bv 8)) <- eval (extract v_3 0 8);
      v_5 <- getRegister (lhs.of_reg xmm_1);
      (v_6 : expression (bv 8)) <- eval (extract v_5 0 8);
      (v_7 : expression (bv 8)) <- eval (extract v_3 8 16);
      (v_8 : expression (bv 8)) <- eval (extract v_5 8 16);
      (v_9 : expression (bv 8)) <- eval (extract v_3 16 24);
      (v_10 : expression (bv 8)) <- eval (extract v_5 16 24);
      (v_11 : expression (bv 8)) <- eval (extract v_3 24 32);
      (v_12 : expression (bv 8)) <- eval (extract v_5 24 32);
      (v_13 : expression (bv 8)) <- eval (extract v_3 32 40);
      (v_14 : expression (bv 8)) <- eval (extract v_5 32 40);
      (v_15 : expression (bv 8)) <- eval (extract v_3 40 48);
      (v_16 : expression (bv 8)) <- eval (extract v_5 40 48);
      (v_17 : expression (bv 8)) <- eval (extract v_3 48 56);
      (v_18 : expression (bv 8)) <- eval (extract v_5 48 56);
      (v_19 : expression (bv 8)) <- eval (extract v_3 56 64);
      (v_20 : expression (bv 8)) <- eval (extract v_5 56 64);
      setRegister (lhs.of_reg xmm_1) (concat (concat v_4 v_6) (concat (concat v_7 v_8) (concat (concat v_9 v_10) (concat (concat v_11 v_12) (concat (concat v_13 v_14) (concat (concat v_15 v_16) (concat (concat v_17 v_18) (concat v_19 v_20))))))));
      pure ()
    pat_end;
    pattern fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) => do
      v_2 <- getRegister (lhs.of_reg xmm_0);
      (v_3 : expression (bv 8)) <- eval (extract v_2 0 8);
      v_4 <- getRegister (lhs.of_reg xmm_1);
      (v_5 : expression (bv 8)) <- eval (extract v_4 0 8);
      (v_6 : expression (bv 8)) <- eval (extract v_2 8 16);
      (v_7 : expression (bv 8)) <- eval (extract v_4 8 16);
      (v_8 : expression (bv 8)) <- eval (extract v_2 16 24);
      (v_9 : expression (bv 8)) <- eval (extract v_4 16 24);
      (v_10 : expression (bv 8)) <- eval (extract v_2 24 32);
      (v_11 : expression (bv 8)) <- eval (extract v_4 24 32);
      (v_12 : expression (bv 8)) <- eval (extract v_2 32 40);
      (v_13 : expression (bv 8)) <- eval (extract v_4 32 40);
      (v_14 : expression (bv 8)) <- eval (extract v_2 40 48);
      (v_15 : expression (bv 8)) <- eval (extract v_4 40 48);
      (v_16 : expression (bv 8)) <- eval (extract v_2 48 56);
      (v_17 : expression (bv 8)) <- eval (extract v_4 48 56);
      (v_18 : expression (bv 8)) <- eval (extract v_2 56 64);
      (v_19 : expression (bv 8)) <- eval (extract v_4 56 64);
      setRegister (lhs.of_reg xmm_1) (concat (concat v_3 v_5) (concat (concat v_6 v_7) (concat (concat v_8 v_9) (concat (concat v_10 v_11) (concat (concat v_12 v_13) (concat (concat v_14 v_15) (concat (concat v_16 v_17) (concat v_18 v_19))))))));
      pure ()
    pat_end
