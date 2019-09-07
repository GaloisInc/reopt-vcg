def pmovzxbw1 : instruction :=
  definst "pmovzxbw" $ do
    pattern fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) => do
      v_2 <- evaluateAddress mem_0;
      v_3 <- load v_2 8;
      setRegister (lhs.of_reg xmm_1) (concat (expression.bv_nat 8 0) (concat (extract v_3 0 8) (concat (expression.bv_nat 8 0) (concat (extract v_3 8 16) (concat (expression.bv_nat 8 0) (concat (extract v_3 16 24) (concat (expression.bv_nat 8 0) (concat (extract v_3 24 32) (concat (expression.bv_nat 8 0) (concat (extract v_3 32 40) (concat (expression.bv_nat 8 0) (concat (extract v_3 40 48) (concat (expression.bv_nat 8 0) (concat (extract v_3 48 56) (concat (expression.bv_nat 8 0) (extract v_3 56 64))))))))))))))));
      pure ()
    pat_end;
    pattern fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) => do
      v_2 <- getRegister xmm_0;
      setRegister (lhs.of_reg xmm_1) (concat (expression.bv_nat 8 0) (concat (extract v_2 64 72) (concat (expression.bv_nat 8 0) (concat (extract v_2 72 80) (concat (expression.bv_nat 8 0) (concat (extract v_2 80 88) (concat (expression.bv_nat 8 0) (concat (extract v_2 88 96) (concat (expression.bv_nat 8 0) (concat (extract v_2 96 104) (concat (expression.bv_nat 8 0) (concat (extract v_2 104 112) (concat (expression.bv_nat 8 0) (concat (extract v_2 112 120) (concat (expression.bv_nat 8 0) (extract v_2 120 128))))))))))))))));
      pure ()
    pat_end
