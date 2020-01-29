def pmuludq : instruction :=
  definst "pmuludq" $ do
    pattern fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) => do
      v_2 <- getRegister (lhs.of_reg xmm_1);
      (v_3 : expression (bv 32)) <- eval (extract v_2 32 64);
      v_4 <- evaluateAddress mem_0;
      v_5 <- load v_4 16;
      (v_6 : expression (bv 32)) <- eval (extract v_5 32 64);
      (v_7 : expression (bv 32)) <- eval (extract v_2 96 128);
      (v_8 : expression (bv 32)) <- eval (extract v_5 96 128);
      setRegister (lhs.of_reg xmm_1) (concat (mul (concat (expression.bv_nat 32 0) v_3) (concat (expression.bv_nat 32 0) v_6)) (mul (concat (expression.bv_nat 32 0) v_7) (concat (expression.bv_nat 32 0) v_8)));
      pure ()
    pat_end;
    pattern fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) => do
      v_2 <- getRegister (lhs.of_reg xmm_1);
      (v_3 : expression (bv 32)) <- eval (extract v_2 32 64);
      v_4 <- getRegister (lhs.of_reg xmm_0);
      (v_5 : expression (bv 32)) <- eval (extract v_4 32 64);
      (v_6 : expression (bv 32)) <- eval (extract v_2 96 128);
      (v_7 : expression (bv 32)) <- eval (extract v_4 96 128);
      setRegister (lhs.of_reg xmm_1) (concat (mul (concat (expression.bv_nat 32 0) v_3) (concat (expression.bv_nat 32 0) v_5)) (mul (concat (expression.bv_nat 32 0) v_6) (concat (expression.bv_nat 32 0) v_7)));
      pure ()
    pat_end
