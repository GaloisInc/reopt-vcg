def pcmpeqq1 : instruction :=
  definst "pcmpeqq" $ do
    pattern fun (v_3280 : reg (bv 128)) (v_3281 : reg (bv 128)) => do
      v_6909 <- getRegister v_3281;
      v_6911 <- getRegister v_3280;
      setRegister (lhs.of_reg v_3281) (concat (mux (eq (extract v_6909 0 64) (extract v_6911 0 64)) (expression.bv_nat 64 18446744073709551615) (expression.bv_nat 64 0)) (mux (eq (extract v_6909 64 128) (extract v_6911 64 128)) (expression.bv_nat 64 18446744073709551615) (expression.bv_nat 64 0)));
      pure ()
    pat_end;
    pattern fun (v_3276 : Mem) (v_3277 : reg (bv 128)) => do
      v_10940 <- getRegister v_3277;
      v_10942 <- evaluateAddress v_3276;
      v_10943 <- load v_10942 16;
      setRegister (lhs.of_reg v_3277) (concat (mux (eq (extract v_10940 0 64) (extract v_10943 0 64)) (expression.bv_nat 64 18446744073709551615) (expression.bv_nat 64 0)) (mux (eq (extract v_10940 64 128) (extract v_10943 64 128)) (expression.bv_nat 64 18446744073709551615) (expression.bv_nat 64 0)));
      pure ()
    pat_end
