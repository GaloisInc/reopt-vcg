def vcvtpd2dq1 : instruction :=
  definst "vcvtpd2dq" $ do
    pattern fun (v_3129 : reg (bv 128)) (v_3130 : reg (bv 128)) => do
      v_5849 <- getRegister v_3129;
      setRegister (lhs.of_reg v_3130) (concat (expression.bv_nat 64 0) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_double_to_int32_truncate (extract v_5849 0 64)) (_(_)_MINT-WRAPPER-SYNTAX cvt_double_to_int32_truncate (extract v_5849 64 128))));
      pure ()
    pat_end;
    pattern fun (v_3131 : reg (bv 256)) (v_3135 : reg (bv 128)) => do
      v_5857 <- getRegister v_3131;
      setRegister (lhs.of_reg v_3135) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_double_to_int32_truncate (extract v_5857 0 64)) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_double_to_int32_truncate (extract v_5857 64 128)) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_double_to_int32_truncate (extract v_5857 128 192)) (_(_)_MINT-WRAPPER-SYNTAX cvt_double_to_int32_truncate (extract v_5857 192 256)))));
      pure ()
    pat_end;
    pattern fun (v_3122 : Mem) (v_3125 : reg (bv 128)) => do
      v_9981 <- evaluateAddress v_3122;
      v_9982 <- load v_9981 32;
      setRegister (lhs.of_reg v_3125) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_double_to_int32_truncate (extract v_9982 0 64)) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_double_to_int32_truncate (extract v_9982 64 128)) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_double_to_int32_truncate (extract v_9982 128 192)) (_(_)_MINT-WRAPPER-SYNTAX cvt_double_to_int32_truncate (extract v_9982 192 256)))));
      pure ()
    pat_end
