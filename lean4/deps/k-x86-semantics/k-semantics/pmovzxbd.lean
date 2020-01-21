def pmovzxbd : instruction :=
  definst "pmovzxbd" $ do
    pattern fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) => do
      v_2 <- evaluateAddress mem_0;
      v_3 <- load v_2 4;
      setRegister (lhs.of_reg xmm_1) (concat (expression.bv_nat 24 0) (concat (extract v_3 0 8) (concat (expression.bv_nat 24 0) (concat (extract v_3 8 16) (concat (expression.bv_nat 24 0) (concat (extract v_3 16 24) (concat (expression.bv_nat 24 0) (extract v_3 24 32))))))));
      pure ()
    pat_end;
    pattern fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) => do
      v_2 <- getRegister (lhs.of_reg xmm_0);
      setRegister (lhs.of_reg xmm_1) (concat (expression.bv_nat 24 0) (concat (extract v_2 96 104) (concat (expression.bv_nat 24 0) (concat (extract v_2 104 112) (concat (expression.bv_nat 24 0) (concat (extract v_2 112 120) (concat (expression.bv_nat 24 0) (extract v_2 120 128))))))));
      pure ()
    pat_end
