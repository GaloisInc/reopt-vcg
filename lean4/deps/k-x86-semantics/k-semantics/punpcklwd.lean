def punpcklwd : instruction :=
  definst "punpcklwd" $ do
    pattern fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) => do
      v_2 <- evaluateAddress mem_0;
      v_3 <- load v_2 16;
      (v_4 : expression (bv 16)) <- eval (extract v_3 64 80);
      v_5 <- getRegister (lhs.of_reg xmm_1);
      (v_6 : expression (bv 16)) <- eval (extract v_5 64 80);
      (v_7 : expression (bv 16)) <- eval (extract v_3 80 96);
      (v_8 : expression (bv 16)) <- eval (extract v_5 80 96);
      (v_9 : expression (bv 16)) <- eval (extract v_3 96 112);
      (v_10 : expression (bv 16)) <- eval (extract v_5 96 112);
      (v_11 : expression (bv 16)) <- eval (extract v_3 112 128);
      (v_12 : expression (bv 16)) <- eval (extract v_5 112 128);
      setRegister (lhs.of_reg xmm_1) (concat (concat v_4 v_6) (concat (concat v_7 v_8) (concat (concat v_9 v_10) (concat v_11 v_12))));
      pure ()
    pat_end;
    pattern fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) => do
      v_2 <- getRegister (lhs.of_reg xmm_0);
      (v_3 : expression (bv 16)) <- eval (extract v_2 64 80);
      v_4 <- getRegister (lhs.of_reg xmm_1);
      (v_5 : expression (bv 16)) <- eval (extract v_4 64 80);
      (v_6 : expression (bv 16)) <- eval (extract v_2 80 96);
      (v_7 : expression (bv 16)) <- eval (extract v_4 80 96);
      (v_8 : expression (bv 16)) <- eval (extract v_2 96 112);
      (v_9 : expression (bv 16)) <- eval (extract v_4 96 112);
      (v_10 : expression (bv 16)) <- eval (extract v_2 112 128);
      (v_11 : expression (bv 16)) <- eval (extract v_4 112 128);
      setRegister (lhs.of_reg xmm_1) (concat (concat v_3 v_5) (concat (concat v_6 v_7) (concat (concat v_8 v_9) (concat v_10 v_11))));
      pure ()
    pat_end
