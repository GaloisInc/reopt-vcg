def vcvttpd2dq1 : instruction :=
  definst "vcvttpd2dq" $ do
    pattern fun (v_3369 : reg (bv 128)) (v_3370 : reg (bv 128)) => do
      v_6272 <- getRegister v_3369;
      setRegister (lhs.of_reg v_3370) (concat (expression.bv_nat 64 0) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_double_to_int32_truncate (extract v_6272 0 64)) (_(_)_MINT-WRAPPER-SYNTAX cvt_double_to_int32_truncate (extract v_6272 64 128))));
      pure ()
    pat_end;
    pattern fun (v_3371 : reg (bv 256)) (v_3375 : reg (bv 128)) => do
      v_6280 <- getRegister v_3371;
      setRegister (lhs.of_reg v_3375) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_double_to_int32_truncate (extract v_6280 0 64)) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_double_to_int32_truncate (extract v_6280 64 128)) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_double_to_int32_truncate (extract v_6280 128 192)) (_(_)_MINT-WRAPPER-SYNTAX cvt_double_to_int32_truncate (extract v_6280 192 256)))));
      pure ()
    pat_end;
    pattern fun (v_3362 : Mem) (v_3365 : reg (bv 128)) => do
      v_10286 <- evaluateAddress v_3362;
      v_10287 <- load v_10286 16;
      setRegister (lhs.of_reg v_3365) (concat (expression.bv_nat 64 0) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_double_to_int32_truncate (extract v_10287 0 64)) (_(_)_MINT-WRAPPER-SYNTAX cvt_double_to_int32_truncate (extract v_10287 64 128))));
      pure ()
    pat_end;
    pattern fun (v_3362 : Mem) (v_3365 : reg (bv 128)) => do
      v_10295 <- evaluateAddress v_3362;
      v_10296 <- load v_10295 16;
      setRegister (lhs.of_reg v_3365) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_double_to_int32_truncate (extract v_10296 0 64)) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_double_to_int32_truncate (extract v_10296 64 128)) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_double_to_int32_truncate (extract v_10296 128 192)) (_(_)_MINT-WRAPPER-SYNTAX cvt_double_to_int32_truncate (extract v_10296 192 256)))));
      pure ()
    pat_end;
    pattern fun (v_3362 : Mem) (v_3365 : reg (bv 128)) => do
      v_10309 <- evaluateAddress v_3362;
      v_10310 <- load v_10309 32;
      setRegister (lhs.of_reg v_3365) (concat (expression.bv_nat 64 0) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_double_to_int32_truncate (extract v_10310 0 64)) (_(_)_MINT-WRAPPER-SYNTAX cvt_double_to_int32_truncate (extract v_10310 64 128))));
      pure ()
    pat_end;
    pattern fun (v_3362 : Mem) (v_3365 : reg (bv 128)) => do
      v_10318 <- evaluateAddress v_3362;
      v_10319 <- load v_10318 32;
      setRegister (lhs.of_reg v_3365) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_double_to_int32_truncate (extract v_10319 0 64)) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_double_to_int32_truncate (extract v_10319 64 128)) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_double_to_int32_truncate (extract v_10319 128 192)) (_(_)_MINT-WRAPPER-SYNTAX cvt_double_to_int32_truncate (extract v_10319 192 256)))));
      pure ()
    pat_end
