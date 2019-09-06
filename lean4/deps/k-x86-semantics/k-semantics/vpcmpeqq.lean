def vpcmpeqq1 : instruction :=
  definst "vpcmpeqq" $ do
    pattern fun (v_2894 : reg (bv 128)) (v_2895 : reg (bv 128)) (v_2896 : reg (bv 128)) => do
      v_7378 <- getRegister v_2895;
      v_7380 <- getRegister v_2894;
      setRegister (lhs.of_reg v_2896) (concat (mux (eq (extract v_7378 0 64) (extract v_7380 0 64)) (expression.bv_nat 64 18446744073709551615) (expression.bv_nat 64 0)) (mux (eq (extract v_7378 64 128) (extract v_7380 64 128)) (expression.bv_nat 64 18446744073709551615) (expression.bv_nat 64 0)));
      pure ()
    pat_end;
    pattern fun (v_2905 : reg (bv 256)) (v_2906 : reg (bv 256)) (v_2907 : reg (bv 256)) => do
      v_7395 <- getRegister v_2906;
      v_7397 <- getRegister v_2905;
      setRegister (lhs.of_reg v_2907) (concat (mux (eq (extract v_7395 0 64) (extract v_7397 0 64)) (expression.bv_nat 64 18446744073709551615) (expression.bv_nat 64 0)) (concat (mux (eq (extract v_7395 64 128) (extract v_7397 64 128)) (expression.bv_nat 64 18446744073709551615) (expression.bv_nat 64 0)) (concat (mux (eq (extract v_7395 128 192) (extract v_7397 128 192)) (expression.bv_nat 64 18446744073709551615) (expression.bv_nat 64 0)) (mux (eq (extract v_7395 192 256) (extract v_7397 192 256)) (expression.bv_nat 64 18446744073709551615) (expression.bv_nat 64 0)))));
      pure ()
    pat_end;
    pattern fun (v_2889 : Mem) (v_2890 : reg (bv 128)) (v_2891 : reg (bv 128)) => do
      v_15978 <- getRegister v_2890;
      v_15980 <- evaluateAddress v_2889;
      v_15981 <- load v_15980 16;
      setRegister (lhs.of_reg v_2891) (concat (mux (eq (extract v_15978 0 64) (extract v_15981 0 64)) (expression.bv_nat 64 18446744073709551615) (expression.bv_nat 64 0)) (mux (eq (extract v_15978 64 128) (extract v_15981 64 128)) (expression.bv_nat 64 18446744073709551615) (expression.bv_nat 64 0)));
      pure ()
    pat_end;
    pattern fun (v_2900 : Mem) (v_2901 : reg (bv 256)) (v_2902 : reg (bv 256)) => do
      v_15991 <- getRegister v_2901;
      v_15993 <- evaluateAddress v_2900;
      v_15994 <- load v_15993 32;
      setRegister (lhs.of_reg v_2902) (concat (mux (eq (extract v_15991 0 64) (extract v_15994 0 64)) (expression.bv_nat 64 18446744073709551615) (expression.bv_nat 64 0)) (concat (mux (eq (extract v_15991 64 128) (extract v_15994 64 128)) (expression.bv_nat 64 18446744073709551615) (expression.bv_nat 64 0)) (concat (mux (eq (extract v_15991 128 192) (extract v_15994 128 192)) (expression.bv_nat 64 18446744073709551615) (expression.bv_nat 64 0)) (mux (eq (extract v_15991 192 256) (extract v_15994 192 256)) (expression.bv_nat 64 18446744073709551615) (expression.bv_nat 64 0)))));
      pure ()
    pat_end
