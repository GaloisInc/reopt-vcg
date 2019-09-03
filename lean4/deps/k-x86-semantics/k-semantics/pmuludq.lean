def pmuludq1 : instruction :=
  definst "pmuludq" $ do
    pattern fun (v_2842 : reg (bv 128)) (v_2843 : reg (bv 128)) => do
      v_5909 <- getRegister v_2843;
      v_5912 <- getRegister v_2842;
      setRegister (lhs.of_reg v_2843) (concat (mul (concat (expression.bv_nat 32 0) (extract v_5909 32 64)) (concat (expression.bv_nat 32 0) (extract v_5912 32 64))) (mul (concat (expression.bv_nat 32 0) (extract v_5909 96 128)) (concat (expression.bv_nat 32 0) (extract v_5912 96 128))));
      pure ()
    pat_end;
    pattern fun (v_2838 : Mem) (v_2839 : reg (bv 128)) => do
      v_12828 <- getRegister v_2839;
      v_12831 <- evaluateAddress v_2838;
      v_12832 <- load v_12831 16;
      setRegister (lhs.of_reg v_2839) (concat (mul (concat (expression.bv_nat 32 0) (extract v_12828 32 64)) (concat (expression.bv_nat 32 0) (extract v_12832 32 64))) (mul (concat (expression.bv_nat 32 0) (extract v_12828 96 128)) (concat (expression.bv_nat 32 0) (extract v_12832 96 128))));
      pure ()
    pat_end
