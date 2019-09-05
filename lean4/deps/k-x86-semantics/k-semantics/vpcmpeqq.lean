def vpcmpeqq1 : instruction :=
  definst "vpcmpeqq" $ do
    pattern fun (v_2868 : reg (bv 128)) (v_2869 : reg (bv 128)) (v_2870 : reg (bv 128)) => do
      v_7351 <- getRegister v_2869;
      v_7353 <- getRegister v_2868;
      setRegister (lhs.of_reg v_2870) (concat (mux (eq (extract v_7351 0 64) (extract v_7353 0 64)) (expression.bv_nat 64 18446744073709551615) (expression.bv_nat 64 0)) (mux (eq (extract v_7351 64 128) (extract v_7353 64 128)) (expression.bv_nat 64 18446744073709551615) (expression.bv_nat 64 0)));
      pure ()
    pat_end;
    pattern fun (v_2878 : reg (bv 256)) (v_2879 : reg (bv 256)) (v_2880 : reg (bv 256)) => do
      v_7368 <- getRegister v_2879;
      v_7370 <- getRegister v_2878;
      setRegister (lhs.of_reg v_2880) (concat (mux (eq (extract v_7368 0 64) (extract v_7370 0 64)) (expression.bv_nat 64 18446744073709551615) (expression.bv_nat 64 0)) (concat (mux (eq (extract v_7368 64 128) (extract v_7370 64 128)) (expression.bv_nat 64 18446744073709551615) (expression.bv_nat 64 0)) (concat (mux (eq (extract v_7368 128 192) (extract v_7370 128 192)) (expression.bv_nat 64 18446744073709551615) (expression.bv_nat 64 0)) (mux (eq (extract v_7368 192 256) (extract v_7370 192 256)) (expression.bv_nat 64 18446744073709551615) (expression.bv_nat 64 0)))));
      pure ()
    pat_end;
    pattern fun (v_2862 : Mem) (v_2863 : reg (bv 128)) (v_2864 : reg (bv 128)) => do
      v_15951 <- getRegister v_2863;
      v_15953 <- evaluateAddress v_2862;
      v_15954 <- load v_15953 16;
      setRegister (lhs.of_reg v_2864) (concat (mux (eq (extract v_15951 0 64) (extract v_15954 0 64)) (expression.bv_nat 64 18446744073709551615) (expression.bv_nat 64 0)) (mux (eq (extract v_15951 64 128) (extract v_15954 64 128)) (expression.bv_nat 64 18446744073709551615) (expression.bv_nat 64 0)));
      pure ()
    pat_end;
    pattern fun (v_2873 : Mem) (v_2874 : reg (bv 256)) (v_2875 : reg (bv 256)) => do
      v_15964 <- getRegister v_2874;
      v_15966 <- evaluateAddress v_2873;
      v_15967 <- load v_15966 32;
      setRegister (lhs.of_reg v_2875) (concat (mux (eq (extract v_15964 0 64) (extract v_15967 0 64)) (expression.bv_nat 64 18446744073709551615) (expression.bv_nat 64 0)) (concat (mux (eq (extract v_15964 64 128) (extract v_15967 64 128)) (expression.bv_nat 64 18446744073709551615) (expression.bv_nat 64 0)) (concat (mux (eq (extract v_15964 128 192) (extract v_15967 128 192)) (expression.bv_nat 64 18446744073709551615) (expression.bv_nat 64 0)) (mux (eq (extract v_15964 192 256) (extract v_15967 192 256)) (expression.bv_nat 64 18446744073709551615) (expression.bv_nat 64 0)))));
      pure ()
    pat_end
