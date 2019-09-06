def vpcmpgtq1 : instruction :=
  definst "vpcmpgtq" $ do
    pattern fun (v_2982 : reg (bv 128)) (v_2983 : reg (bv 128)) (v_2984 : reg (bv 128)) => do
      v_7884 <- getRegister v_2983;
      v_7886 <- getRegister v_2982;
      setRegister (lhs.of_reg v_2984) (concat (mux (sgt (extract v_7884 0 64) (extract v_7886 0 64)) (expression.bv_nat 64 18446744073709551615) (expression.bv_nat 64 0)) (mux (sgt (extract v_7884 64 128) (extract v_7886 64 128)) (expression.bv_nat 64 18446744073709551615) (expression.bv_nat 64 0)));
      pure ()
    pat_end;
    pattern fun (v_2993 : reg (bv 256)) (v_2994 : reg (bv 256)) (v_2995 : reg (bv 256)) => do
      v_7901 <- getRegister v_2994;
      v_7903 <- getRegister v_2993;
      setRegister (lhs.of_reg v_2995) (concat (mux (sgt (extract v_7901 0 64) (extract v_7903 0 64)) (expression.bv_nat 64 18446744073709551615) (expression.bv_nat 64 0)) (concat (mux (sgt (extract v_7901 64 128) (extract v_7903 64 128)) (expression.bv_nat 64 18446744073709551615) (expression.bv_nat 64 0)) (concat (mux (sgt (extract v_7901 128 192) (extract v_7903 128 192)) (expression.bv_nat 64 18446744073709551615) (expression.bv_nat 64 0)) (mux (sgt (extract v_7901 192 256) (extract v_7903 192 256)) (expression.bv_nat 64 18446744073709551615) (expression.bv_nat 64 0)))));
      pure ()
    pat_end;
    pattern fun (v_2977 : Mem) (v_2978 : reg (bv 128)) (v_2979 : reg (bv 128)) => do
      v_16452 <- getRegister v_2978;
      v_16454 <- evaluateAddress v_2977;
      v_16455 <- load v_16454 16;
      setRegister (lhs.of_reg v_2979) (concat (mux (sgt (extract v_16452 0 64) (extract v_16455 0 64)) (expression.bv_nat 64 18446744073709551615) (expression.bv_nat 64 0)) (mux (sgt (extract v_16452 64 128) (extract v_16455 64 128)) (expression.bv_nat 64 18446744073709551615) (expression.bv_nat 64 0)));
      pure ()
    pat_end;
    pattern fun (v_2988 : Mem) (v_2989 : reg (bv 256)) (v_2990 : reg (bv 256)) => do
      v_16465 <- getRegister v_2989;
      v_16467 <- evaluateAddress v_2988;
      v_16468 <- load v_16467 32;
      setRegister (lhs.of_reg v_2990) (concat (mux (sgt (extract v_16465 0 64) (extract v_16468 0 64)) (expression.bv_nat 64 18446744073709551615) (expression.bv_nat 64 0)) (concat (mux (sgt (extract v_16465 64 128) (extract v_16468 64 128)) (expression.bv_nat 64 18446744073709551615) (expression.bv_nat 64 0)) (concat (mux (sgt (extract v_16465 128 192) (extract v_16468 128 192)) (expression.bv_nat 64 18446744073709551615) (expression.bv_nat 64 0)) (mux (sgt (extract v_16465 192 256) (extract v_16468 192 256)) (expression.bv_nat 64 18446744073709551615) (expression.bv_nat 64 0)))));
      pure ()
    pat_end
