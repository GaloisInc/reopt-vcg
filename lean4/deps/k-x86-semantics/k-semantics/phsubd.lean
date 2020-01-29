def phsubd : instruction :=
  definst "phsubd" $ do
    pattern fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) => do
      v_2 <- evaluateAddress mem_0;
      v_3 <- load v_2 16;
      (v_4 : expression (bv 32)) <- eval (extract v_3 32 64);
      (v_5 : expression (bv 32)) <- eval (extract v_3 0 32);
      (v_6 : expression (bv 32)) <- eval (extract v_3 96 128);
      (v_7 : expression (bv 32)) <- eval (extract v_3 64 96);
      v_8 <- getRegister (lhs.of_reg xmm_1);
      (v_9 : expression (bv 32)) <- eval (extract v_8 32 64);
      (v_10 : expression (bv 32)) <- eval (extract v_8 0 32);
      (v_11 : expression (bv 32)) <- eval (extract v_8 96 128);
      (v_12 : expression (bv 32)) <- eval (extract v_8 64 96);
      setRegister (lhs.of_reg xmm_1) (concat (concat (concat (sub v_4 v_5) (sub v_6 v_7)) (sub v_9 v_10)) (sub v_11 v_12));
      pure ()
    pat_end;
    pattern fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) => do
      v_2 <- getRegister (lhs.of_reg xmm_0);
      (v_3 : expression (bv 32)) <- eval (extract v_2 32 64);
      (v_4 : expression (bv 32)) <- eval (extract v_2 0 32);
      (v_5 : expression (bv 32)) <- eval (extract v_2 96 128);
      (v_6 : expression (bv 32)) <- eval (extract v_2 64 96);
      v_7 <- getRegister (lhs.of_reg xmm_1);
      (v_8 : expression (bv 32)) <- eval (extract v_7 32 64);
      (v_9 : expression (bv 32)) <- eval (extract v_7 0 32);
      (v_10 : expression (bv 32)) <- eval (extract v_7 96 128);
      (v_11 : expression (bv 32)) <- eval (extract v_7 64 96);
      setRegister (lhs.of_reg xmm_1) (concat (concat (concat (sub v_3 v_4) (sub v_5 v_6)) (sub v_8 v_9)) (sub v_10 v_11));
      pure ()
    pat_end
