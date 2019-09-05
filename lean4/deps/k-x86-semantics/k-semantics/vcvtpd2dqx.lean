def vcvtpd2dqx1 : instruction :=
  definst "vcvtpd2dqx" $ do
    pattern fun (v_3111 : Mem) (v_3112 : reg (bv 128)) => do
      v_9968 <- evaluateAddress v_3111;
      v_9969 <- load v_9968 16;
      setRegister (lhs.of_reg v_3112) (concat (expression.bv_nat 64 0) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_double_to_int32_truncate (extract v_9969 0 64)) (_(_)_MINT-WRAPPER-SYNTAX cvt_double_to_int32_truncate (extract v_9969 64 128))));
      pure ()
    pat_end
