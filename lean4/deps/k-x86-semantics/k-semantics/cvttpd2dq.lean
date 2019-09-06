def cvttpd2dq1 : instruction :=
  definst "cvttpd2dq" $ do
    pattern fun (v_2706 : reg (bv 128)) (v_2707 : reg (bv 128)) => do
      v_4316 <- getRegister v_2706;
      setRegister (lhs.of_reg v_2707) (concat (expression.bv_nat 64 0) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_double_to_int32_truncate (extract v_4316 0 64)) (_(_)_MINT-WRAPPER-SYNTAX cvt_double_to_int32_truncate (extract v_4316 64 128))));
      pure ()
    pat_end;
    pattern fun (v_2702 : Mem) (v_2703 : reg (bv 128)) => do
      v_7986 <- evaluateAddress v_2702;
      v_7987 <- load v_7986 16;
      setRegister (lhs.of_reg v_2703) (concat (expression.bv_nat 64 0) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_double_to_int32_truncate (extract v_7987 0 64)) (_(_)_MINT-WRAPPER-SYNTAX cvt_double_to_int32_truncate (extract v_7987 64 128))));
      pure ()
    pat_end
