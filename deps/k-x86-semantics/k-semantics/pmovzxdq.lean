def pmovzxdq : instruction :=
  definst "pmovzxdq" $ do
    pattern fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) => do
      v_2 <- evaluateAddress mem_0;
      v_3 <- load v_2 8;
      (v_4 : expression (bv 32)) <- eval (extract v_3 0 32);
      (v_5 : expression (bv 32)) <- eval (extract v_3 32 64);
      setRegister (lhs.of_reg xmm_1) (concat (expression.bv_nat 32 0) (concat v_4 (concat (expression.bv_nat 32 0) v_5)));
      pure ()
    pat_end;
    pattern fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) => do
      v_2 <- getRegister (lhs.of_reg xmm_0);
      (v_3 : expression (bv 32)) <- eval (extract v_2 64 96);
      (v_4 : expression (bv 32)) <- eval (extract v_2 96 128);
      setRegister (lhs.of_reg xmm_1) (concat (expression.bv_nat 32 0) (concat v_3 (concat (expression.bv_nat 32 0) v_4)));
      pure ()
    pat_end
