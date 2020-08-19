def pmovzxbq : instruction :=
  definst "pmovzxbq" $ do
    pattern fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) => do
      v_2 <- evaluateAddress mem_0;
      v_3 <- load v_2 2;
      (v_4 : expression (bv 8)) <- eval (extract v_3 0 8);
      (v_5 : expression (bv 8)) <- eval (extract v_3 8 16);
      setRegister (lhs.of_reg xmm_1) (concat (expression.bv_nat 56 0) (concat v_4 (concat (expression.bv_nat 56 0) v_5)));
      pure ()
    pat_end;
    pattern fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) => do
      v_2 <- getRegister (lhs.of_reg xmm_0);
      (v_3 : expression (bv 8)) <- eval (extract v_2 112 120);
      (v_4 : expression (bv 8)) <- eval (extract v_2 120 128);
      setRegister (lhs.of_reg xmm_1) (concat (expression.bv_nat 56 0) (concat v_3 (concat (expression.bv_nat 56 0) v_4)));
      pure ()
    pat_end