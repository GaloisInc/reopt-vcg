def vcvtpd2dqx1 : instruction :=
  definst "vcvtpd2dqx" $ do
    pattern fun (v_3045 : Mem) (v_3048 : reg (bv 128)) => do
      v_10206 <- evaluateAddress v_3045;
      v_10207 <- load v_10206 16;
      setRegister (lhs.of_reg v_3048) (concat (expression.bv_nat 64 0) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_double_to_int32_truncate (extract v_10207 0 64)) (_(_)_MINT-WRAPPER-SYNTAX cvt_double_to_int32_truncate (extract v_10207 64 128))));
      pure ()
    pat_end
