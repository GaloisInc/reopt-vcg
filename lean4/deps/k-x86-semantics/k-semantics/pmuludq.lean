def pmuludq1 : instruction :=
  definst "pmuludq" $ do
    pattern fun (v_2828 : reg (bv 128)) (v_2829 : reg (bv 128)) => do
      v_6058 <- getRegister v_2829;
      v_6061 <- getRegister v_2828;
      setRegister (lhs.of_reg v_2829) (concat (mul (concat (expression.bv_nat 32 0) (extract v_6058 32 64)) (concat (expression.bv_nat 32 0) (extract v_6061 32 64))) (mul (concat (expression.bv_nat 32 0) (extract v_6058 96 128)) (concat (expression.bv_nat 32 0) (extract v_6061 96 128))));
      pure ()
    pat_end;
    pattern fun (v_2823 : Mem) (v_2824 : reg (bv 128)) => do
      v_13303 <- getRegister v_2824;
      v_13306 <- evaluateAddress v_2823;
      v_13307 <- load v_13306 16;
      setRegister (lhs.of_reg v_2824) (concat (mul (concat (expression.bv_nat 32 0) (extract v_13303 32 64)) (concat (expression.bv_nat 32 0) (extract v_13307 32 64))) (mul (concat (expression.bv_nat 32 0) (extract v_13303 96 128)) (concat (expression.bv_nat 32 0) (extract v_13307 96 128))));
      pure ()
    pat_end
