def vcvttpd2dq1 : instruction :=
  definst "vcvttpd2dq" $ do
    pattern fun (v_3291 : reg (bv 128)) (v_3292 : reg (bv 128)) => do
      v_7010 <- getRegister v_3291;
      setRegister (lhs.of_reg v_3292) (concat (expression.bv_nat 64 0) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_double_to_int32_truncate (extract v_7010 0 64)) (_(_)_MINT-WRAPPER-SYNTAX cvt_double_to_int32_truncate (extract v_7010 64 128))));
      pure ()
    pat_end;
    pattern fun (v_3293 : reg (bv 256)) (v_3297 : reg (bv 128)) => do
      v_7018 <- getRegister v_3293;
      setRegister (lhs.of_reg v_3297) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_double_to_int32_truncate (extract v_7018 0 64)) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_double_to_int32_truncate (extract v_7018 64 128)) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_double_to_int32_truncate (extract v_7018 128 192)) (_(_)_MINT-WRAPPER-SYNTAX cvt_double_to_int32_truncate (extract v_7018 192 256)))));
      pure ()
    pat_end;
    pattern fun (v_3284 : Mem) (v_3287 : reg (bv 128)) => do
      v_12231 <- evaluateAddress v_3284;
      v_12232 <- load v_12231 16;
      setRegister (lhs.of_reg v_3287) (concat (expression.bv_nat 64 0) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_double_to_int32_truncate (extract v_12232 0 64)) (_(_)_MINT-WRAPPER-SYNTAX cvt_double_to_int32_truncate (extract v_12232 64 128))));
      pure ()
    pat_end;
    pattern fun (v_3284 : Mem) (v_3287 : reg (bv 128)) => do
      v_12240 <- evaluateAddress v_3284;
      v_12241 <- load v_12240 16;
      setRegister (lhs.of_reg v_3287) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_double_to_int32_truncate (extract v_12241 0 64)) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_double_to_int32_truncate (extract v_12241 64 128)) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_double_to_int32_truncate (extract v_12241 128 192)) (_(_)_MINT-WRAPPER-SYNTAX cvt_double_to_int32_truncate (extract v_12241 192 256)))));
      pure ()
    pat_end;
    pattern fun (v_3284 : Mem) (v_3287 : reg (bv 128)) => do
      v_12254 <- evaluateAddress v_3284;
      v_12255 <- load v_12254 32;
      setRegister (lhs.of_reg v_3287) (concat (expression.bv_nat 64 0) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_double_to_int32_truncate (extract v_12255 0 64)) (_(_)_MINT-WRAPPER-SYNTAX cvt_double_to_int32_truncate (extract v_12255 64 128))));
      pure ()
    pat_end;
    pattern fun (v_3284 : Mem) (v_3287 : reg (bv 128)) => do
      v_12263 <- evaluateAddress v_3284;
      v_12264 <- load v_12263 32;
      setRegister (lhs.of_reg v_3287) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_double_to_int32_truncate (extract v_12264 0 64)) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_double_to_int32_truncate (extract v_12264 64 128)) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_double_to_int32_truncate (extract v_12264 128 192)) (_(_)_MINT-WRAPPER-SYNTAX cvt_double_to_int32_truncate (extract v_12264 192 256)))));
      pure ()
    pat_end
