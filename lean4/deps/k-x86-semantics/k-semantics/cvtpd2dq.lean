def cvtpd2dq1 : instruction :=
  definst "cvtpd2dq" $ do
    pattern fun (v_2572 : reg (bv 128)) (v_2573 : reg (bv 128)) => do
      v_4142 <- getRegister v_2572;
      setRegister (lhs.of_reg v_2573) (concat (expression.bv_nat 64 0) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_double_to_int32_truncate (extract v_4142 0 64)) (_(_)_MINT-WRAPPER-SYNTAX cvt_double_to_int32_truncate (extract v_4142 64 128))));
      pure ()
    pat_end;
    pattern fun (v_2568 : Mem) (v_2569 : reg (bv 128)) => do
      v_7841 <- evaluateAddress v_2568;
      v_7842 <- load v_7841 16;
      setRegister (lhs.of_reg v_2569) (concat (expression.bv_nat 64 0) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_double_to_int32_truncate (extract v_7842 0 64)) (_(_)_MINT-WRAPPER-SYNTAX cvt_double_to_int32_truncate (extract v_7842 64 128))));
      pure ()
    pat_end
