def cvttpd2dq1 : instruction :=
  definst "cvttpd2dq" $ do
    pattern fun (v_2680 : reg (bv 128)) (v_2681 : reg (bv 128)) => do
      v_4295 <- getRegister v_2680;
      setRegister (lhs.of_reg v_2681) (concat (expression.bv_nat 64 0) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_double_to_int32_truncate (extract v_4295 0 64)) (_(_)_MINT-WRAPPER-SYNTAX cvt_double_to_int32_truncate (extract v_4295 64 128))));
      pure ()
    pat_end;
    pattern fun (v_2675 : Mem) (v_2676 : reg (bv 128)) => do
      v_7976 <- evaluateAddress v_2675;
      v_7977 <- load v_7976 16;
      setRegister (lhs.of_reg v_2676) (concat (expression.bv_nat 64 0) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_double_to_int32_truncate (extract v_7977 0 64)) (_(_)_MINT-WRAPPER-SYNTAX cvt_double_to_int32_truncate (extract v_7977 64 128))));
      pure ()
    pat_end
