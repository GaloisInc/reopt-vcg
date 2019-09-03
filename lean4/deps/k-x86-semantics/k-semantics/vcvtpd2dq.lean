def vcvtpd2dq1 : instruction :=
  definst "vcvtpd2dq" $ do
    pattern fun (v_3038 : reg (bv 128)) (v_3039 : reg (bv 128)) => do
      v_5900 <- getRegister v_3038;
      setRegister (lhs.of_reg v_3039) (concat (expression.bv_nat 64 0) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_double_to_int32_truncate (extract v_5900 0 64)) (_(_)_MINT-WRAPPER-SYNTAX cvt_double_to_int32_truncate (extract v_5900 64 128))));
      pure ()
    pat_end;
    pattern fun (v_3041 : reg (bv 256)) (v_3044 : reg (bv 128)) => do
      v_5908 <- getRegister v_3041;
      setRegister (lhs.of_reg v_3044) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_double_to_int32_truncate (extract v_5908 0 64)) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_double_to_int32_truncate (extract v_5908 64 128)) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_double_to_int32_truncate (extract v_5908 128 192)) (_(_)_MINT-WRAPPER-SYNTAX cvt_double_to_int32_truncate (extract v_5908 192 256)))));
      pure ()
    pat_end;
    pattern fun (v_3031 : Mem) (v_3034 : reg (bv 128)) => do
      v_10192 <- evaluateAddress v_3031;
      v_10193 <- load v_10192 32;
      setRegister (lhs.of_reg v_3034) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_double_to_int32_truncate (extract v_10193 0 64)) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_double_to_int32_truncate (extract v_10193 64 128)) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_double_to_int32_truncate (extract v_10193 128 192)) (_(_)_MINT-WRAPPER-SYNTAX cvt_double_to_int32_truncate (extract v_10193 192 256)))));
      pure ()
    pat_end
