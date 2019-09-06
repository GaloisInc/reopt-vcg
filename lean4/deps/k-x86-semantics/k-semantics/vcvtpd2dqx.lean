def vcvtpd2dqx1 : instruction :=
  definst "vcvtpd2dqx" $ do
    pattern fun (v_3136 : Mem) (v_3139 : reg (bv 128)) => do
      v_9995 <- evaluateAddress v_3136;
      v_9996 <- load v_9995 16;
      setRegister (lhs.of_reg v_3139) (concat (expression.bv_nat 64 0) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_double_to_int32_truncate (extract v_9996 0 64)) (_(_)_MINT-WRAPPER-SYNTAX cvt_double_to_int32_truncate (extract v_9996 64 128))));
      pure ()
    pat_end
