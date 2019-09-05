def vpmovzxdq1 : instruction :=
  definst "vpmovzxdq" $ do
    pattern fun (v_2818 : reg (bv 128)) (v_2819 : reg (bv 128)) => do
      v_5882 <- getRegister v_2818;
      setRegister (lhs.of_reg v_2819) (concat (expression.bv_nat 32 0) (concat (extract v_5882 64 96) (concat (expression.bv_nat 32 0) (extract v_5882 96 128))));
      pure ()
    pat_end;
    pattern fun (v_2828 : reg (bv 128)) (v_2827 : reg (bv 256)) => do
      v_5893 <- getRegister v_2828;
      setRegister (lhs.of_reg v_2827) (concat (expression.bv_nat 32 0) (concat (extract v_5893 0 32) (concat (expression.bv_nat 32 0) (concat (extract v_5893 32 64) (concat (expression.bv_nat 32 0) (concat (extract v_5893 64 96) (concat (expression.bv_nat 32 0) (extract v_5893 96 128))))))));
      pure ()
    pat_end;
    pattern fun (v_2813 : Mem) (v_2814 : reg (bv 128)) => do
      v_12259 <- evaluateAddress v_2813;
      v_12260 <- load v_12259 8;
      setRegister (lhs.of_reg v_2814) (concat (expression.bv_nat 32 0) (concat (extract v_12260 0 32) (concat (expression.bv_nat 32 0) (extract v_12260 32 64))));
      pure ()
    pat_end;
    pattern fun (v_2822 : Mem) (v_2823 : reg (bv 256)) => do
      v_12267 <- evaluateAddress v_2822;
      v_12268 <- load v_12267 16;
      setRegister (lhs.of_reg v_2823) (concat (expression.bv_nat 32 0) (concat (extract v_12268 0 32) (concat (expression.bv_nat 32 0) (concat (extract v_12268 32 64) (concat (expression.bv_nat 32 0) (concat (extract v_12268 64 96) (concat (expression.bv_nat 32 0) (extract v_12268 96 128))))))));
      pure ()
    pat_end
