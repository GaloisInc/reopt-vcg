def vcvttpd2dq1 : instruction :=
  definst "vcvttpd2dq" $ do
    pattern fun (v_3278 : reg (bv 128)) (v_3279 : reg (bv 128)) => do
      v_6323 <- getRegister v_3278;
      setRegister (lhs.of_reg v_3279) (concat (expression.bv_nat 64 0) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_double_to_int32_truncate (extract v_6323 0 64)) (_(_)_MINT-WRAPPER-SYNTAX cvt_double_to_int32_truncate (extract v_6323 64 128))));
      pure ()
    pat_end;
    pattern fun (v_3281 : reg (bv 256)) (v_3284 : reg (bv 128)) => do
      v_6331 <- getRegister v_3281;
      setRegister (lhs.of_reg v_3284) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_double_to_int32_truncate (extract v_6331 0 64)) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_double_to_int32_truncate (extract v_6331 64 128)) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_double_to_int32_truncate (extract v_6331 128 192)) (_(_)_MINT-WRAPPER-SYNTAX cvt_double_to_int32_truncate (extract v_6331 192 256)))));
      pure ()
    pat_end;
    pattern fun (v_3271 : Mem) (v_3274 : reg (bv 128)) => do
      v_10497 <- evaluateAddress v_3271;
      v_10498 <- load v_10497 16;
      setRegister (lhs.of_reg v_3274) (concat (expression.bv_nat 64 0) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_double_to_int32_truncate (extract v_10498 0 64)) (_(_)_MINT-WRAPPER-SYNTAX cvt_double_to_int32_truncate (extract v_10498 64 128))));
      pure ()
    pat_end;
    pattern fun (v_3271 : Mem) (v_3274 : reg (bv 128)) => do
      v_10506 <- evaluateAddress v_3271;
      v_10507 <- load v_10506 16;
      setRegister (lhs.of_reg v_3274) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_double_to_int32_truncate (extract v_10507 0 64)) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_double_to_int32_truncate (extract v_10507 64 128)) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_double_to_int32_truncate (extract v_10507 128 192)) (_(_)_MINT-WRAPPER-SYNTAX cvt_double_to_int32_truncate (extract v_10507 192 256)))));
      pure ()
    pat_end;
    pattern fun (v_3271 : Mem) (v_3274 : reg (bv 128)) => do
      v_10520 <- evaluateAddress v_3271;
      v_10521 <- load v_10520 32;
      setRegister (lhs.of_reg v_3274) (concat (expression.bv_nat 64 0) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_double_to_int32_truncate (extract v_10521 0 64)) (_(_)_MINT-WRAPPER-SYNTAX cvt_double_to_int32_truncate (extract v_10521 64 128))));
      pure ()
    pat_end;
    pattern fun (v_3271 : Mem) (v_3274 : reg (bv 128)) => do
      v_10529 <- evaluateAddress v_3271;
      v_10530 <- load v_10529 32;
      setRegister (lhs.of_reg v_3274) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_double_to_int32_truncate (extract v_10530 0 64)) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_double_to_int32_truncate (extract v_10530 64 128)) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_double_to_int32_truncate (extract v_10530 128 192)) (_(_)_MINT-WRAPPER-SYNTAX cvt_double_to_int32_truncate (extract v_10530 192 256)))));
      pure ()
    pat_end
