def pmovzxwq1 : instruction :=
  definst "pmovzxwq" $ do
    pattern fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) => do
      v_2 <- evaluateAddress mem_0;
      v_3 <- load v_2 4;
      setRegister (lhs.of_reg xmm_1) (concat (expression.bv_nat 48 0) (concat (extract v_3 0 16) (concat (expression.bv_nat 48 0) (extract v_3 16 32))));
      pure ()
    pat_end;
    pattern fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) => do
      v_2 <- getRegister xmm_0;
      setRegister (lhs.of_reg xmm_1) (concat (expression.bv_nat 48 0) (concat (extract v_2 96 112) (concat (expression.bv_nat 48 0) (extract v_2 112 128))));
      pure ()
    pat_end
