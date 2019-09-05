def vcvtpd2dq1 : instruction :=
  definst "vcvtpd2dq" $ do
    pattern fun (v_3102 : reg (bv 128)) (v_3103 : reg (bv 128)) => do
      v_5822 <- getRegister v_3102;
      setRegister (lhs.of_reg v_3103) (concat (expression.bv_nat 64 0) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_double_to_int32_truncate (extract v_5822 0 64)) (_(_)_MINT-WRAPPER-SYNTAX cvt_double_to_int32_truncate (extract v_5822 64 128))));
      pure ()
    pat_end;
    pattern fun (v_3106 : reg (bv 256)) (v_3108 : reg (bv 128)) => do
      v_5830 <- getRegister v_3106;
      setRegister (lhs.of_reg v_3108) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_double_to_int32_truncate (extract v_5830 0 64)) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_double_to_int32_truncate (extract v_5830 64 128)) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_double_to_int32_truncate (extract v_5830 128 192)) (_(_)_MINT-WRAPPER-SYNTAX cvt_double_to_int32_truncate (extract v_5830 192 256)))));
      pure ()
    pat_end;
    pattern fun (v_3097 : Mem) (v_3098 : reg (bv 128)) => do
      v_9954 <- evaluateAddress v_3097;
      v_9955 <- load v_9954 32;
      setRegister (lhs.of_reg v_3098) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_double_to_int32_truncate (extract v_9955 0 64)) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_double_to_int32_truncate (extract v_9955 64 128)) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_double_to_int32_truncate (extract v_9955 128 192)) (_(_)_MINT-WRAPPER-SYNTAX cvt_double_to_int32_truncate (extract v_9955 192 256)))));
      pure ()
    pat_end
