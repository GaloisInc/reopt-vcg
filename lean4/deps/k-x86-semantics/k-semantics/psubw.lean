def psubw : instruction :=
  definst "psubw" $ do
    pattern fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) => do
      v_2 <- getRegister (lhs.of_reg xmm_1);
      (v_3 : expression (bv 16)) <- eval (extract v_2 0 16);
      v_4 <- evaluateAddress mem_0;
      v_5 <- load v_4 16;
      (v_6 : expression (bv 16)) <- eval (extract v_5 0 16);
      (v_7 : expression (bv 16)) <- eval (extract v_2 16 32);
      (v_8 : expression (bv 16)) <- eval (extract v_5 16 32);
      (v_9 : expression (bv 16)) <- eval (extract v_2 32 48);
      (v_10 : expression (bv 16)) <- eval (extract v_5 32 48);
      (v_11 : expression (bv 16)) <- eval (extract v_2 48 64);
      (v_12 : expression (bv 16)) <- eval (extract v_5 48 64);
      (v_13 : expression (bv 16)) <- eval (extract v_2 64 80);
      (v_14 : expression (bv 16)) <- eval (extract v_5 64 80);
      (v_15 : expression (bv 16)) <- eval (extract v_2 80 96);
      (v_16 : expression (bv 16)) <- eval (extract v_5 80 96);
      (v_17 : expression (bv 16)) <- eval (extract v_2 96 112);
      (v_18 : expression (bv 16)) <- eval (extract v_5 96 112);
      (v_19 : expression (bv 16)) <- eval (extract v_2 112 128);
      (v_20 : expression (bv 16)) <- eval (extract v_5 112 128);
      setRegister (lhs.of_reg xmm_1) (concat (sub v_3 v_6) (concat (sub v_7 v_8) (concat (sub v_9 v_10) (concat (sub v_11 v_12) (concat (sub v_13 v_14) (concat (sub v_15 v_16) (concat (sub v_17 v_18) (sub v_19 v_20))))))));
      pure ()
    pat_end;
    pattern fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) => do
      v_2 <- getRegister (lhs.of_reg xmm_1);
      (v_3 : expression (bv 16)) <- eval (extract v_2 0 16);
      v_4 <- getRegister (lhs.of_reg xmm_0);
      (v_5 : expression (bv 16)) <- eval (extract v_4 0 16);
      (v_6 : expression (bv 16)) <- eval (extract v_2 16 32);
      (v_7 : expression (bv 16)) <- eval (extract v_4 16 32);
      (v_8 : expression (bv 16)) <- eval (extract v_2 32 48);
      (v_9 : expression (bv 16)) <- eval (extract v_4 32 48);
      (v_10 : expression (bv 16)) <- eval (extract v_2 48 64);
      (v_11 : expression (bv 16)) <- eval (extract v_4 48 64);
      (v_12 : expression (bv 16)) <- eval (extract v_2 64 80);
      (v_13 : expression (bv 16)) <- eval (extract v_4 64 80);
      (v_14 : expression (bv 16)) <- eval (extract v_2 80 96);
      (v_15 : expression (bv 16)) <- eval (extract v_4 80 96);
      (v_16 : expression (bv 16)) <- eval (extract v_2 96 112);
      (v_17 : expression (bv 16)) <- eval (extract v_4 96 112);
      (v_18 : expression (bv 16)) <- eval (extract v_2 112 128);
      (v_19 : expression (bv 16)) <- eval (extract v_4 112 128);
      setRegister (lhs.of_reg xmm_1) (concat (sub v_3 v_5) (concat (sub v_6 v_7) (concat (sub v_8 v_9) (concat (sub v_10 v_11) (concat (sub v_12 v_13) (concat (sub v_14 v_15) (concat (sub v_16 v_17) (sub v_18 v_19))))))));
      pure ()
    pat_end
