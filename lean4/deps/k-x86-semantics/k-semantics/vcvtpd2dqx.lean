def vcvtpd2dqx1 : instruction :=
  definst "vcvtpd2dqx" $ do
    pattern fun (v_3058 : Mem) (v_3061 : reg (bv 128)) => do
      v_11748 <- evaluateAddress v_3058;
      v_11749 <- load v_11748 16;
      setRegister (lhs.of_reg v_3061) (concat (expression.bv_nat 64 0) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_double_to_int32_truncate (extract v_11749 0 64)) (_(_)_MINT-WRAPPER-SYNTAX cvt_double_to_int32_truncate (extract v_11749 64 128))));
      pure ()
    pat_end
