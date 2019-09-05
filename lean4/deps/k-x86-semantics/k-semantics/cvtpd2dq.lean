def cvtpd2dq1 : instruction :=
  definst "cvtpd2dq" $ do
    pattern fun (v_2546 : reg (bv 128)) (v_2547 : reg (bv 128)) => do
      v_4121 <- getRegister v_2546;
      setRegister (lhs.of_reg v_2547) (concat (expression.bv_nat 64 0) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_double_to_int32_truncate (extract v_4121 0 64)) (_(_)_MINT-WRAPPER-SYNTAX cvt_double_to_int32_truncate (extract v_4121 64 128))));
      pure ()
    pat_end;
    pattern fun (v_2541 : Mem) (v_2542 : reg (bv 128)) => do
      v_7831 <- evaluateAddress v_2541;
      v_7832 <- load v_7831 16;
      setRegister (lhs.of_reg v_2542) (concat (expression.bv_nat 64 0) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_double_to_int32_truncate (extract v_7832 0 64)) (_(_)_MINT-WRAPPER-SYNTAX cvt_double_to_int32_truncate (extract v_7832 64 128))));
      pure ()
    pat_end
