def cvtpd2dq1 : instruction :=
  definst "cvtpd2dq" $ do
    pattern fun (v_2494 : reg (bv 128)) (v_2495 : reg (bv 128)) => do
      v_4097 <- getRegister v_2494;
      setRegister (lhs.of_reg v_2495) (concat (expression.bv_nat 64 0) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_double_to_int32_truncate (extract v_4097 0 64)) (_(_)_MINT-WRAPPER-SYNTAX cvt_double_to_int32_truncate (extract v_4097 64 128))));
      pure ()
    pat_end;
    pattern fun (v_2488 : Mem) (v_2490 : reg (bv 128)) => do
      v_8325 <- evaluateAddress v_2488;
      v_8326 <- load v_8325 16;
      setRegister (lhs.of_reg v_2490) (concat (expression.bv_nat 64 0) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_double_to_int32_truncate (extract v_8326 0 64)) (_(_)_MINT-WRAPPER-SYNTAX cvt_double_to_int32_truncate (extract v_8326 64 128))));
      pure ()
    pat_end
