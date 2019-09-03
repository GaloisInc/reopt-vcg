def cvtpd2dq1 : instruction :=
  definst "cvtpd2dq" $ do
    pattern fun (v_2481 : reg (bv 128)) (v_2482 : reg (bv 128)) => do
      v_4111 <- getRegister v_2481;
      setRegister (lhs.of_reg v_2482) (concat (expression.bv_nat 64 0) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_double_to_int32_truncate (extract v_4111 0 64)) (_(_)_MINT-WRAPPER-SYNTAX cvt_double_to_int32_truncate (extract v_4111 64 128))));
      pure ()
    pat_end;
    pattern fun (v_2477 : Mem) (v_2478 : reg (bv 128)) => do
      v_8053 <- evaluateAddress v_2477;
      v_8054 <- load v_8053 16;
      setRegister (lhs.of_reg v_2478) (concat (expression.bv_nat 64 0) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_double_to_int32_truncate (extract v_8054 0 64)) (_(_)_MINT-WRAPPER-SYNTAX cvt_double_to_int32_truncate (extract v_8054 64 128))));
      pure ()
    pat_end
