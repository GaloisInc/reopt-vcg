def pmaxud1 : instruction :=
  definst "pmaxud" $ do
    pattern fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) => do
      v_2 <- getRegister xmm_1;
      v_3 <- eval (extract v_2 0 32);
      v_4 <- evaluateAddress mem_0;
      v_5 <- load v_4 16;
      v_6 <- eval (extract v_5 0 32);
      v_7 <- eval (extract v_2 32 64);
      v_8 <- eval (extract v_5 32 64);
      v_9 <- eval (extract v_2 64 96);
      v_10 <- eval (extract v_5 64 96);
      v_11 <- eval (extract v_2 96 128);
      v_12 <- eval (extract v_5 96 128);
      setRegister (lhs.of_reg xmm_1) (concat (mux (ugt v_3 v_6) v_3 v_6) (concat (mux (ugt v_7 v_8) v_7 v_8) (concat (mux (ugt v_9 v_10) v_9 v_10) (mux (ugt v_11 v_12) v_11 v_12))));
      pure ()
    pat_end;
    pattern fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) => do
      v_2 <- getRegister xmm_1;
      v_3 <- eval (extract v_2 0 32);
      v_4 <- getRegister xmm_0;
      v_5 <- eval (extract v_4 0 32);
      v_6 <- eval (extract v_2 32 64);
      v_7 <- eval (extract v_4 32 64);
      v_8 <- eval (extract v_2 64 96);
      v_9 <- eval (extract v_4 64 96);
      v_10 <- eval (extract v_2 96 128);
      v_11 <- eval (extract v_4 96 128);
      setRegister (lhs.of_reg xmm_1) (concat (mux (ugt v_3 v_5) v_3 v_5) (concat (mux (ugt v_6 v_7) v_6 v_7) (concat (mux (ugt v_8 v_9) v_8 v_9) (mux (ugt v_10 v_11) v_10 v_11))));
      pure ()
    pat_end
