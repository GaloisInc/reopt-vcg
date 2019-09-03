def vcvtpd2dq1 : instruction :=
  definst "vcvtpd2dq" $ do
    pattern fun (v_3051 : reg (bv 128)) (v_3052 : reg (bv 128)) => do
      v_6359 <- getRegister v_3051;
      setRegister (lhs.of_reg v_3052) (concat (expression.bv_nat 64 0) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_double_to_int32_truncate (extract v_6359 0 64)) (_(_)_MINT-WRAPPER-SYNTAX cvt_double_to_int32_truncate (extract v_6359 64 128))));
      pure ()
    pat_end;
    pattern fun (v_3053 : reg (bv 256)) (v_3057 : reg (bv 128)) => do
      v_6367 <- getRegister v_3053;
      setRegister (lhs.of_reg v_3057) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_double_to_int32_truncate (extract v_6367 0 64)) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_double_to_int32_truncate (extract v_6367 64 128)) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_double_to_int32_truncate (extract v_6367 128 192)) (_(_)_MINT-WRAPPER-SYNTAX cvt_double_to_int32_truncate (extract v_6367 192 256)))));
      pure ()
    pat_end;
    pattern fun (v_3044 : Mem) (v_3047 : reg (bv 128)) => do
      v_11734 <- evaluateAddress v_3044;
      v_11735 <- load v_11734 32;
      setRegister (lhs.of_reg v_3047) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_double_to_int32_truncate (extract v_11735 0 64)) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_double_to_int32_truncate (extract v_11735 64 128)) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_double_to_int32_truncate (extract v_11735 128 192)) (_(_)_MINT-WRAPPER-SYNTAX cvt_double_to_int32_truncate (extract v_11735 192 256)))));
      pure ()
    pat_end
