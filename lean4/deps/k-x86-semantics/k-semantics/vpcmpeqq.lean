def vpcmpeqq1 : instruction :=
  definst "vpcmpeqq" $ do
    pattern fun (v_2814 : reg (bv 128)) (v_2815 : reg (bv 128)) (v_2816 : reg (bv 128)) => do
      v_7450 <- getRegister v_2815;
      v_7452 <- getRegister v_2814;
      setRegister (lhs.of_reg v_2816) (concat (mux (eq (extract v_7450 0 64) (extract v_7452 0 64)) (expression.bv_nat 64 18446744073709551615) (expression.bv_nat 64 0)) (mux (eq (extract v_7450 64 128) (extract v_7452 64 128)) (expression.bv_nat 64 18446744073709551615) (expression.bv_nat 64 0)));
      pure ()
    pat_end;
    pattern fun (v_2828 : reg (bv 256)) (v_2829 : reg (bv 256)) (v_2830 : reg (bv 256)) => do
      v_7467 <- getRegister v_2829;
      v_7469 <- getRegister v_2828;
      setRegister (lhs.of_reg v_2830) (concat (mux (eq (extract v_7467 0 64) (extract v_7469 0 64)) (expression.bv_nat 64 18446744073709551615) (expression.bv_nat 64 0)) (concat (mux (eq (extract v_7467 64 128) (extract v_7469 64 128)) (expression.bv_nat 64 18446744073709551615) (expression.bv_nat 64 0)) (concat (mux (eq (extract v_7467 128 192) (extract v_7469 128 192)) (expression.bv_nat 64 18446744073709551615) (expression.bv_nat 64 0)) (mux (eq (extract v_7467 192 256) (extract v_7469 192 256)) (expression.bv_nat 64 18446744073709551615) (expression.bv_nat 64 0)))));
      pure ()
    pat_end;
    pattern fun (v_2813 : Mem) (v_2809 : reg (bv 128)) (v_2810 : reg (bv 128)) => do
      v_16298 <- getRegister v_2809;
      v_16300 <- evaluateAddress v_2813;
      v_16301 <- load v_16300 16;
      setRegister (lhs.of_reg v_2810) (concat (mux (eq (extract v_16298 0 64) (extract v_16301 0 64)) (expression.bv_nat 64 18446744073709551615) (expression.bv_nat 64 0)) (mux (eq (extract v_16298 64 128) (extract v_16301 64 128)) (expression.bv_nat 64 18446744073709551615) (expression.bv_nat 64 0)));
      pure ()
    pat_end;
    pattern fun (v_2822 : Mem) (v_2823 : reg (bv 256)) (v_2824 : reg (bv 256)) => do
      v_16311 <- getRegister v_2823;
      v_16313 <- evaluateAddress v_2822;
      v_16314 <- load v_16313 32;
      setRegister (lhs.of_reg v_2824) (concat (mux (eq (extract v_16311 0 64) (extract v_16314 0 64)) (expression.bv_nat 64 18446744073709551615) (expression.bv_nat 64 0)) (concat (mux (eq (extract v_16311 64 128) (extract v_16314 64 128)) (expression.bv_nat 64 18446744073709551615) (expression.bv_nat 64 0)) (concat (mux (eq (extract v_16311 128 192) (extract v_16314 128 192)) (expression.bv_nat 64 18446744073709551615) (expression.bv_nat 64 0)) (mux (eq (extract v_16311 192 256) (extract v_16314 192 256)) (expression.bv_nat 64 18446744073709551615) (expression.bv_nat 64 0)))));
      pure ()
    pat_end
