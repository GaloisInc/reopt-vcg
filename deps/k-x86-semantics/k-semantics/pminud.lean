def pminud : instruction :=
  definst "pminud" $ do
    pattern fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) => do
      v_2 <- getRegister (lhs.of_reg xmm_1);
      (v_3 : expression (bv 32)) <- eval (extract v_2 0 32);
      v_4 <- evaluateAddress mem_0;
      v_5 <- load v_4 16;
      (v_6 : expression (bv 32)) <- eval (extract v_5 0 32);
      (v_7 : expression (bv 32)) <- eval (extract v_2 32 64);
      (v_8 : expression (bv 32)) <- eval (extract v_5 32 64);
      (v_9 : expression (bv 32)) <- eval (extract v_2 64 96);
      (v_10 : expression (bv 32)) <- eval (extract v_5 64 96);
      (v_11 : expression (bv 32)) <- eval (extract v_2 96 128);
      (v_12 : expression (bv 32)) <- eval (extract v_5 96 128);
      setRegister (lhs.of_reg xmm_1) (concat (mux (ult v_3 v_6) v_3 v_6) (concat (mux (ult v_7 v_8) v_7 v_8) (concat (mux (ult v_9 v_10) v_9 v_10) (mux (ult v_11 v_12) v_11 v_12))));
      pure ()
    pat_end;
    pattern fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) => do
      v_2 <- getRegister (lhs.of_reg xmm_1);
      (v_3 : expression (bv 32)) <- eval (extract v_2 0 32);
      v_4 <- getRegister (lhs.of_reg xmm_0);
      (v_5 : expression (bv 32)) <- eval (extract v_4 0 32);
      (v_6 : expression (bv 32)) <- eval (extract v_2 32 64);
      (v_7 : expression (bv 32)) <- eval (extract v_4 32 64);
      (v_8 : expression (bv 32)) <- eval (extract v_2 64 96);
      (v_9 : expression (bv 32)) <- eval (extract v_4 64 96);
      (v_10 : expression (bv 32)) <- eval (extract v_2 96 128);
      (v_11 : expression (bv 32)) <- eval (extract v_4 96 128);
      setRegister (lhs.of_reg xmm_1) (concat (mux (ult v_3 v_5) v_3 v_5) (concat (mux (ult v_6 v_7) v_6 v_7) (concat (mux (ult v_8 v_9) v_8 v_9) (mux (ult v_10 v_11) v_10 v_11))));
      pure ()
    pat_end
