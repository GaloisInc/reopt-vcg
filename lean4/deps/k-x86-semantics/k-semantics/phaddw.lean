def phaddw : instruction :=
  definst "phaddw" $ do
    pattern fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) => do
      v_2 <- evaluateAddress mem_0;
      v_3 <- load v_2 16;
      (v_4 : expression (bv 16)) <- eval (extract v_3 0 16);
      (v_5 : expression (bv 16)) <- eval (extract v_3 16 32);
      (v_6 : expression (bv 16)) <- eval (extract v_3 32 48);
      (v_7 : expression (bv 16)) <- eval (extract v_3 48 64);
      (v_8 : expression (bv 16)) <- eval (extract v_3 64 80);
      (v_9 : expression (bv 16)) <- eval (extract v_3 80 96);
      (v_10 : expression (bv 16)) <- eval (extract v_3 96 112);
      (v_11 : expression (bv 16)) <- eval (extract v_3 112 128);
      v_12 <- getRegister (lhs.of_reg xmm_1);
      (v_13 : expression (bv 16)) <- eval (extract v_12 0 16);
      (v_14 : expression (bv 16)) <- eval (extract v_12 16 32);
      (v_15 : expression (bv 16)) <- eval (extract v_12 32 48);
      (v_16 : expression (bv 16)) <- eval (extract v_12 48 64);
      (v_17 : expression (bv 16)) <- eval (extract v_12 64 80);
      (v_18 : expression (bv 16)) <- eval (extract v_12 80 96);
      (v_19 : expression (bv 16)) <- eval (extract v_12 96 112);
      (v_20 : expression (bv 16)) <- eval (extract v_12 112 128);
      setRegister (lhs.of_reg xmm_1) (concat (concat (concat (concat (concat (concat (concat (add v_4 v_5) (add v_6 v_7)) (add v_8 v_9)) (add v_10 v_11)) (add v_13 v_14)) (add v_15 v_16)) (add v_17 v_18)) (add v_19 v_20));
      pure ()
    pat_end;
    pattern fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) => do
      v_2 <- getRegister (lhs.of_reg xmm_0);
      (v_3 : expression (bv 16)) <- eval (extract v_2 0 16);
      (v_4 : expression (bv 16)) <- eval (extract v_2 16 32);
      (v_5 : expression (bv 16)) <- eval (extract v_2 32 48);
      (v_6 : expression (bv 16)) <- eval (extract v_2 48 64);
      (v_7 : expression (bv 16)) <- eval (extract v_2 64 80);
      (v_8 : expression (bv 16)) <- eval (extract v_2 80 96);
      (v_9 : expression (bv 16)) <- eval (extract v_2 96 112);
      (v_10 : expression (bv 16)) <- eval (extract v_2 112 128);
      v_11 <- getRegister (lhs.of_reg xmm_1);
      (v_12 : expression (bv 16)) <- eval (extract v_11 0 16);
      (v_13 : expression (bv 16)) <- eval (extract v_11 16 32);
      (v_14 : expression (bv 16)) <- eval (extract v_11 32 48);
      (v_15 : expression (bv 16)) <- eval (extract v_11 48 64);
      (v_16 : expression (bv 16)) <- eval (extract v_11 64 80);
      (v_17 : expression (bv 16)) <- eval (extract v_11 80 96);
      (v_18 : expression (bv 16)) <- eval (extract v_11 96 112);
      (v_19 : expression (bv 16)) <- eval (extract v_11 112 128);
      setRegister (lhs.of_reg xmm_1) (concat (concat (concat (concat (concat (concat (concat (add v_3 v_4) (add v_5 v_6)) (add v_7 v_8)) (add v_9 v_10)) (add v_12 v_13)) (add v_14 v_15)) (add v_16 v_17)) (add v_18 v_19));
      pure ()
    pat_end
