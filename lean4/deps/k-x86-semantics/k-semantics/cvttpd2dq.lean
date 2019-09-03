def cvttpd2dq1 : instruction :=
  definst "cvttpd2dq" $ do
    pattern fun (v_2615 : reg (bv 128)) (v_2616 : reg (bv 128)) => do
      v_4285 <- getRegister v_2615;
      setRegister (lhs.of_reg v_2616) (concat (expression.bv_nat 64 0) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_double_to_int32_truncate (extract v_4285 0 64)) (_(_)_MINT-WRAPPER-SYNTAX cvt_double_to_int32_truncate (extract v_4285 64 128))));
      pure ()
    pat_end;
    pattern fun (v_2611 : Mem) (v_2612 : reg (bv 128)) => do
      v_8198 <- evaluateAddress v_2611;
      v_8199 <- load v_8198 16;
      setRegister (lhs.of_reg v_2612) (concat (expression.bv_nat 64 0) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_double_to_int32_truncate (extract v_8199 0 64)) (_(_)_MINT-WRAPPER-SYNTAX cvt_double_to_int32_truncate (extract v_8199 64 128))));
      pure ()
    pat_end
