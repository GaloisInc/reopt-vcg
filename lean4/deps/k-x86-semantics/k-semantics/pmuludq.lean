def pmuludq1 : instruction :=
  definst "pmuludq" $ do
    pattern fun (v_2919 : reg (bv 128)) (v_2920 : reg (bv 128)) => do
      v_5967 <- getRegister v_2920;
      v_5970 <- getRegister v_2919;
      setRegister (lhs.of_reg v_2920) (concat (mul (concat (expression.bv_nat 32 0) (extract v_5967 32 64)) (concat (expression.bv_nat 32 0) (extract v_5970 32 64))) (mul (concat (expression.bv_nat 32 0) (extract v_5967 96 128)) (concat (expression.bv_nat 32 0) (extract v_5970 96 128))));
      pure ()
    pat_end;
    pattern fun (v_2915 : Mem) (v_2916 : reg (bv 128)) => do
      v_12662 <- getRegister v_2916;
      v_12665 <- evaluateAddress v_2915;
      v_12666 <- load v_12665 16;
      setRegister (lhs.of_reg v_2916) (concat (mul (concat (expression.bv_nat 32 0) (extract v_12662 32 64)) (concat (expression.bv_nat 32 0) (extract v_12666 32 64))) (mul (concat (expression.bv_nat 32 0) (extract v_12662 96 128)) (concat (expression.bv_nat 32 0) (extract v_12666 96 128))));
      pure ()
    pat_end
