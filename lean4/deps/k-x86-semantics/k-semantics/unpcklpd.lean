def unpcklpd : instruction :=
  definst "unpcklpd" $ do
    pattern fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) => do
      v_2 <- evaluateAddress mem_0;
      v_3 <- load v_2 16;
      (v_4 : expression (bv 64)) <- eval (extract v_3 64 128);
      v_5 <- getRegister (lhs.of_reg xmm_1);
      (v_6 : expression (bv 64)) <- eval (extract v_5 64 128);
      setRegister (lhs.of_reg xmm_1) (concat v_4 v_6);
      pure ()
    pat_end;
    pattern fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) => do
      v_2 <- getRegister (lhs.of_reg xmm_0);
      (v_3 : expression (bv 64)) <- eval (extract v_2 64 128);
      v_4 <- getRegister (lhs.of_reg xmm_1);
      (v_5 : expression (bv 64)) <- eval (extract v_4 64 128);
      setRegister (lhs.of_reg xmm_1) (concat v_3 v_5);
      pure ()
    pat_end
