def pmovsxbq : instruction :=
  definst "pmovsxbq" $ do
    pattern fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) => do
      v_2 <- evaluateAddress mem_0;
      v_3 <- load v_2 2;
      (v_4 : expression (bv 8)) <- eval (extract v_3 0 8);
      (v_5 : expression (bv 8)) <- eval (extract v_3 8 16);
      setRegister (lhs.of_reg xmm_1) (concat (sext v_4 64) (sext v_5 64));
      pure ()
    pat_end;
    pattern fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) => do
      v_2 <- getRegister (lhs.of_reg xmm_0);
      (v_3 : expression (bv 8)) <- eval (extract v_2 112 120);
      (v_4 : expression (bv 8)) <- eval (extract v_2 120 128);
      setRegister (lhs.of_reg xmm_1) (concat (sext v_3 64) (sext v_4 64));
      pure ()
    pat_end