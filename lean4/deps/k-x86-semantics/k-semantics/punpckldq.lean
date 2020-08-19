def punpckldq : instruction :=
  definst "punpckldq" $ do
    pattern fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) => do
      v_2 <- evaluateAddress mem_0;
      v_3 <- load v_2 16;
      (v_4 : expression (bv 32)) <- eval (extract v_3 64 96);
      v_5 <- getRegister (lhs.of_reg xmm_1);
      (v_6 : expression (bv 32)) <- eval (extract v_5 64 96);
      (v_7 : expression (bv 32)) <- eval (extract v_3 96 128);
      (v_8 : expression (bv 32)) <- eval (extract v_5 96 128);
      setRegister (lhs.of_reg xmm_1) (concat (concat v_4 v_6) (concat v_7 v_8));
      pure ()
    pat_end;
    pattern fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) => do
      v_2 <- getRegister (lhs.of_reg xmm_0);
      (v_3 : expression (bv 32)) <- eval (extract v_2 64 96);
      v_4 <- getRegister (lhs.of_reg xmm_1);
      (v_5 : expression (bv 32)) <- eval (extract v_4 64 96);
      (v_6 : expression (bv 32)) <- eval (extract v_2 96 128);
      (v_7 : expression (bv 32)) <- eval (extract v_4 96 128);
      setRegister (lhs.of_reg xmm_1) (concat (concat v_3 v_5) (concat v_6 v_7));
      pure ()
    pat_end