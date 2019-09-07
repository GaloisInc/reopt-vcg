def pminsw1 : instruction :=
  definst "pminsw" $ do
    pattern fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) => do
      v_2 <- getRegister xmm_1;
      v_3 <- eval (extract v_2 0 16);
      v_4 <- evaluateAddress mem_0;
      v_5 <- load v_4 16;
      v_6 <- eval (extract v_5 0 16);
      v_7 <- eval (extract v_2 16 32);
      v_8 <- eval (extract v_5 16 32);
      v_9 <- eval (extract v_2 32 48);
      v_10 <- eval (extract v_5 32 48);
      v_11 <- eval (extract v_2 48 64);
      v_12 <- eval (extract v_5 48 64);
      v_13 <- eval (extract v_2 64 80);
      v_14 <- eval (extract v_5 64 80);
      v_15 <- eval (extract v_2 80 96);
      v_16 <- eval (extract v_5 80 96);
      v_17 <- eval (extract v_2 96 112);
      v_18 <- eval (extract v_5 96 112);
      v_19 <- eval (extract v_2 112 128);
      v_20 <- eval (extract v_5 112 128);
      setRegister (lhs.of_reg xmm_1) (concat (mux (slt v_3 v_6) v_3 v_6) (concat (mux (slt v_7 v_8) v_7 v_8) (concat (mux (slt v_9 v_10) v_9 v_10) (concat (mux (slt v_11 v_12) v_11 v_12) (concat (mux (slt v_13 v_14) v_13 v_14) (concat (mux (slt v_15 v_16) v_15 v_16) (concat (mux (slt v_17 v_18) v_17 v_18) (mux (slt v_19 v_20) v_19 v_20))))))));
      pure ()
    pat_end;
    pattern fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) => do
      v_2 <- getRegister xmm_1;
      v_3 <- eval (extract v_2 0 16);
      v_4 <- getRegister xmm_0;
      v_5 <- eval (extract v_4 0 16);
      v_6 <- eval (extract v_2 16 32);
      v_7 <- eval (extract v_4 16 32);
      v_8 <- eval (extract v_2 32 48);
      v_9 <- eval (extract v_4 32 48);
      v_10 <- eval (extract v_2 48 64);
      v_11 <- eval (extract v_4 48 64);
      v_12 <- eval (extract v_2 64 80);
      v_13 <- eval (extract v_4 64 80);
      v_14 <- eval (extract v_2 80 96);
      v_15 <- eval (extract v_4 80 96);
      v_16 <- eval (extract v_2 96 112);
      v_17 <- eval (extract v_4 96 112);
      v_18 <- eval (extract v_2 112 128);
      v_19 <- eval (extract v_4 112 128);
      setRegister (lhs.of_reg xmm_1) (concat (mux (slt v_3 v_5) v_3 v_5) (concat (mux (slt v_6 v_7) v_6 v_7) (concat (mux (slt v_8 v_9) v_8 v_9) (concat (mux (slt v_10 v_11) v_10 v_11) (concat (mux (slt v_12 v_13) v_12 v_13) (concat (mux (slt v_14 v_15) v_14 v_15) (concat (mux (slt v_16 v_17) v_16 v_17) (mux (slt v_18 v_19) v_18 v_19))))))));
      pure ()
    pat_end
