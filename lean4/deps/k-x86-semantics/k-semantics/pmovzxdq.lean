def pmovzxdq : instruction :=
  definst "pmovzxdq" $ do
    pattern fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) => do
      v_2 <- evaluateAddress mem_0;
      v_3 <- load v_2 8;
      setRegister (lhs.of_reg xmm_1) (concat (expression.bv_nat 32 0) (concat (extract v_3 0 32) (concat (expression.bv_nat 32 0) (extract v_3 32 64))));
      pure ()
    pat_end;
    pattern fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) => do
      v_2 <- getRegister (lhs.of_reg xmm_0);
      setRegister (lhs.of_reg xmm_1) (concat (expression.bv_nat 32 0) (concat (extract v_2 64 96) (concat (expression.bv_nat 32 0) (extract v_2 96 128))));
      pure ()
    pat_end
