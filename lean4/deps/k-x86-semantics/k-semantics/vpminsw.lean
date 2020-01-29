def vpminsw : instruction :=
  definst "vpminsw" $ do
    pattern fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) => do
      v_3 <- getRegister (lhs.of_reg xmm_1);
      (v_4 : expression (bv 16)) <- eval (extract v_3 0 16);
      v_5 <- evaluateAddress mem_0;
      v_6 <- load v_5 16;
      (v_7 : expression (bv 16)) <- eval (extract v_6 0 16);
      (v_8 : expression (bv 16)) <- eval (extract v_3 16 32);
      (v_9 : expression (bv 16)) <- eval (extract v_6 16 32);
      (v_10 : expression (bv 16)) <- eval (extract v_3 32 48);
      (v_11 : expression (bv 16)) <- eval (extract v_6 32 48);
      (v_12 : expression (bv 16)) <- eval (extract v_3 48 64);
      (v_13 : expression (bv 16)) <- eval (extract v_6 48 64);
      (v_14 : expression (bv 16)) <- eval (extract v_3 64 80);
      (v_15 : expression (bv 16)) <- eval (extract v_6 64 80);
      (v_16 : expression (bv 16)) <- eval (extract v_3 80 96);
      (v_17 : expression (bv 16)) <- eval (extract v_6 80 96);
      (v_18 : expression (bv 16)) <- eval (extract v_3 96 112);
      (v_19 : expression (bv 16)) <- eval (extract v_6 96 112);
      (v_20 : expression (bv 16)) <- eval (extract v_3 112 128);
      (v_21 : expression (bv 16)) <- eval (extract v_6 112 128);
      setRegister (lhs.of_reg xmm_2) (concat (mux (slt v_4 v_7) v_4 v_7) (concat (mux (slt v_8 v_9) v_8 v_9) (concat (mux (slt v_10 v_11) v_10 v_11) (concat (mux (slt v_12 v_13) v_12 v_13) (concat (mux (slt v_14 v_15) v_14 v_15) (concat (mux (slt v_16 v_17) v_16 v_17) (concat (mux (slt v_18 v_19) v_18 v_19) (mux (slt v_20 v_21) v_20 v_21))))))));
      pure ()
    pat_end;
    pattern fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) => do
      v_3 <- getRegister (lhs.of_reg xmm_1);
      (v_4 : expression (bv 16)) <- eval (extract v_3 0 16);
      v_5 <- getRegister (lhs.of_reg xmm_0);
      (v_6 : expression (bv 16)) <- eval (extract v_5 0 16);
      (v_7 : expression (bv 16)) <- eval (extract v_3 16 32);
      (v_8 : expression (bv 16)) <- eval (extract v_5 16 32);
      (v_9 : expression (bv 16)) <- eval (extract v_3 32 48);
      (v_10 : expression (bv 16)) <- eval (extract v_5 32 48);
      (v_11 : expression (bv 16)) <- eval (extract v_3 48 64);
      (v_12 : expression (bv 16)) <- eval (extract v_5 48 64);
      (v_13 : expression (bv 16)) <- eval (extract v_3 64 80);
      (v_14 : expression (bv 16)) <- eval (extract v_5 64 80);
      (v_15 : expression (bv 16)) <- eval (extract v_3 80 96);
      (v_16 : expression (bv 16)) <- eval (extract v_5 80 96);
      (v_17 : expression (bv 16)) <- eval (extract v_3 96 112);
      (v_18 : expression (bv 16)) <- eval (extract v_5 96 112);
      (v_19 : expression (bv 16)) <- eval (extract v_3 112 128);
      (v_20 : expression (bv 16)) <- eval (extract v_5 112 128);
      setRegister (lhs.of_reg xmm_2) (concat (mux (slt v_4 v_6) v_4 v_6) (concat (mux (slt v_7 v_8) v_7 v_8) (concat (mux (slt v_9 v_10) v_9 v_10) (concat (mux (slt v_11 v_12) v_11 v_12) (concat (mux (slt v_13 v_14) v_13 v_14) (concat (mux (slt v_15 v_16) v_15 v_16) (concat (mux (slt v_17 v_18) v_17 v_18) (mux (slt v_19 v_20) v_19 v_20))))))));
      pure ()
    pat_end
