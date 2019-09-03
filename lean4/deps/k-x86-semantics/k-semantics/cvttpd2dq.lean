def cvttpd2dq1 : instruction :=
  definst "cvttpd2dq" $ do
    pattern fun (v_2628 : reg (bv 128)) (v_2629 : reg (bv 128)) => do
      v_4307 <- getRegister v_2628;
      setRegister (lhs.of_reg v_2629) (concat (expression.bv_nat 64 0) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_double_to_int32_truncate (extract v_4307 0 64)) (_(_)_MINT-WRAPPER-SYNTAX cvt_double_to_int32_truncate (extract v_4307 64 128))));
      pure ()
    pat_end;
    pattern fun (v_2622 : Mem) (v_2624 : reg (bv 128)) => do
      v_8506 <- evaluateAddress v_2622;
      v_8507 <- load v_8506 16;
      setRegister (lhs.of_reg v_2624) (concat (expression.bv_nat 64 0) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_double_to_int32_truncate (extract v_8507 0 64)) (_(_)_MINT-WRAPPER-SYNTAX cvt_double_to_int32_truncate (extract v_8507 64 128))));
      pure ()
    pat_end
