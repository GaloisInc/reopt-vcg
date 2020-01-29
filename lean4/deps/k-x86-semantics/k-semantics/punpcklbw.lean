def punpcklbw : instruction :=
  definst "punpcklbw" $ do
    pattern fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) => do
      v_2 <- evaluateAddress mem_0;
      v_3 <- load v_2 16;
      (v_4 : expression (bv 8)) <- eval (extract v_3 64 72);
      v_5 <- getRegister (lhs.of_reg xmm_1);
      (v_6 : expression (bv 8)) <- eval (extract v_5 64 72);
      (v_7 : expression (bv 8)) <- eval (extract v_3 72 80);
      (v_8 : expression (bv 8)) <- eval (extract v_5 72 80);
      (v_9 : expression (bv 8)) <- eval (extract v_3 80 88);
      (v_10 : expression (bv 8)) <- eval (extract v_5 80 88);
      (v_11 : expression (bv 8)) <- eval (extract v_3 88 96);
      (v_12 : expression (bv 8)) <- eval (extract v_5 88 96);
      (v_13 : expression (bv 8)) <- eval (extract v_3 96 104);
      (v_14 : expression (bv 8)) <- eval (extract v_5 96 104);
      (v_15 : expression (bv 8)) <- eval (extract v_3 104 112);
      (v_16 : expression (bv 8)) <- eval (extract v_5 104 112);
      (v_17 : expression (bv 8)) <- eval (extract v_3 112 120);
      (v_18 : expression (bv 8)) <- eval (extract v_5 112 120);
      (v_19 : expression (bv 8)) <- eval (extract v_3 120 128);
      (v_20 : expression (bv 8)) <- eval (extract v_5 120 128);
      setRegister (lhs.of_reg xmm_1) (concat (concat v_4 v_6) (concat (concat v_7 v_8) (concat (concat v_9 v_10) (concat (concat v_11 v_12) (concat (concat v_13 v_14) (concat (concat v_15 v_16) (concat (concat v_17 v_18) (concat v_19 v_20))))))));
      pure ()
    pat_end;
    pattern fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) => do
      v_2 <- getRegister (lhs.of_reg xmm_0);
      (v_3 : expression (bv 8)) <- eval (extract v_2 64 72);
      v_4 <- getRegister (lhs.of_reg xmm_1);
      (v_5 : expression (bv 8)) <- eval (extract v_4 64 72);
      (v_6 : expression (bv 8)) <- eval (extract v_2 72 80);
      (v_7 : expression (bv 8)) <- eval (extract v_4 72 80);
      (v_8 : expression (bv 8)) <- eval (extract v_2 80 88);
      (v_9 : expression (bv 8)) <- eval (extract v_4 80 88);
      (v_10 : expression (bv 8)) <- eval (extract v_2 88 96);
      (v_11 : expression (bv 8)) <- eval (extract v_4 88 96);
      (v_12 : expression (bv 8)) <- eval (extract v_2 96 104);
      (v_13 : expression (bv 8)) <- eval (extract v_4 96 104);
      (v_14 : expression (bv 8)) <- eval (extract v_2 104 112);
      (v_15 : expression (bv 8)) <- eval (extract v_4 104 112);
      (v_16 : expression (bv 8)) <- eval (extract v_2 112 120);
      (v_17 : expression (bv 8)) <- eval (extract v_4 112 120);
      (v_18 : expression (bv 8)) <- eval (extract v_2 120 128);
      (v_19 : expression (bv 8)) <- eval (extract v_4 120 128);
      setRegister (lhs.of_reg xmm_1) (concat (concat v_3 v_5) (concat (concat v_6 v_7) (concat (concat v_8 v_9) (concat (concat v_10 v_11) (concat (concat v_12 v_13) (concat (concat v_14 v_15) (concat (concat v_16 v_17) (concat v_18 v_19))))))));
      pure ()
    pat_end
