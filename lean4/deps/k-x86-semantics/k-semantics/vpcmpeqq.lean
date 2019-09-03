def vpcmpeqq1 : instruction :=
  definst "vpcmpeqq" $ do
    pattern fun (v_2804 : reg (bv 128)) (v_2805 : reg (bv 128)) (v_2806 : reg (bv 128)) => do
      v_7587 <- getRegister v_2805;
      v_7589 <- getRegister v_2804;
      setRegister (lhs.of_reg v_2806) (concat (mux (eq (extract v_7587 0 64) (extract v_7589 0 64)) (expression.bv_nat 64 18446744073709551615) (expression.bv_nat 64 0)) (mux (eq (extract v_7587 64 128) (extract v_7589 64 128)) (expression.bv_nat 64 18446744073709551615) (expression.bv_nat 64 0)));
      pure ()
    pat_end;
    pattern fun (v_2815 : reg (bv 256)) (v_2816 : reg (bv 256)) (v_2817 : reg (bv 256)) => do
      v_7604 <- getRegister v_2816;
      v_7606 <- getRegister v_2815;
      setRegister (lhs.of_reg v_2817) (concat (mux (eq (extract v_7604 0 64) (extract v_7606 0 64)) (expression.bv_nat 64 18446744073709551615) (expression.bv_nat 64 0)) (concat (mux (eq (extract v_7604 64 128) (extract v_7606 64 128)) (expression.bv_nat 64 18446744073709551615) (expression.bv_nat 64 0)) (concat (mux (eq (extract v_7604 128 192) (extract v_7606 128 192)) (expression.bv_nat 64 18446744073709551615) (expression.bv_nat 64 0)) (mux (eq (extract v_7604 192 256) (extract v_7606 192 256)) (expression.bv_nat 64 18446744073709551615) (expression.bv_nat 64 0)))));
      pure ()
    pat_end;
    pattern fun (v_2798 : Mem) (v_2799 : reg (bv 128)) (v_2800 : reg (bv 128)) => do
      v_16807 <- getRegister v_2799;
      v_16809 <- evaluateAddress v_2798;
      v_16810 <- load v_16809 16;
      setRegister (lhs.of_reg v_2800) (concat (mux (eq (extract v_16807 0 64) (extract v_16810 0 64)) (expression.bv_nat 64 18446744073709551615) (expression.bv_nat 64 0)) (mux (eq (extract v_16807 64 128) (extract v_16810 64 128)) (expression.bv_nat 64 18446744073709551615) (expression.bv_nat 64 0)));
      pure ()
    pat_end;
    pattern fun (v_2809 : Mem) (v_2810 : reg (bv 256)) (v_2811 : reg (bv 256)) => do
      v_16820 <- getRegister v_2810;
      v_16822 <- evaluateAddress v_2809;
      v_16823 <- load v_16822 32;
      setRegister (lhs.of_reg v_2811) (concat (mux (eq (extract v_16820 0 64) (extract v_16823 0 64)) (expression.bv_nat 64 18446744073709551615) (expression.bv_nat 64 0)) (concat (mux (eq (extract v_16820 64 128) (extract v_16823 64 128)) (expression.bv_nat 64 18446744073709551615) (expression.bv_nat 64 0)) (concat (mux (eq (extract v_16820 128 192) (extract v_16823 128 192)) (expression.bv_nat 64 18446744073709551615) (expression.bv_nat 64 0)) (mux (eq (extract v_16820 192 256) (extract v_16823 192 256)) (expression.bv_nat 64 18446744073709551615) (expression.bv_nat 64 0)))));
      pure ()
    pat_end
