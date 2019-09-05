def vcvttpd2dq1 : instruction :=
  definst "vcvttpd2dq" $ do
    pattern fun (v_3342 : reg (bv 128)) (v_3343 : reg (bv 128)) => do
      v_6245 <- getRegister v_3342;
      setRegister (lhs.of_reg v_3343) (concat (expression.bv_nat 64 0) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_double_to_int32_truncate (extract v_6245 0 64)) (_(_)_MINT-WRAPPER-SYNTAX cvt_double_to_int32_truncate (extract v_6245 64 128))));
      pure ()
    pat_end;
    pattern fun (v_3346 : reg (bv 256)) (v_3348 : reg (bv 128)) => do
      v_6253 <- getRegister v_3346;
      setRegister (lhs.of_reg v_3348) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_double_to_int32_truncate (extract v_6253 0 64)) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_double_to_int32_truncate (extract v_6253 64 128)) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_double_to_int32_truncate (extract v_6253 128 192)) (_(_)_MINT-WRAPPER-SYNTAX cvt_double_to_int32_truncate (extract v_6253 192 256)))));
      pure ()
    pat_end;
    pattern fun (v_3337 : Mem) (v_3338 : reg (bv 128)) => do
      v_10259 <- evaluateAddress v_3337;
      v_10260 <- load v_10259 16;
      setRegister (lhs.of_reg v_3338) (concat (expression.bv_nat 64 0) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_double_to_int32_truncate (extract v_10260 0 64)) (_(_)_MINT-WRAPPER-SYNTAX cvt_double_to_int32_truncate (extract v_10260 64 128))));
      pure ()
    pat_end;
    pattern fun (v_3337 : Mem) (v_3338 : reg (bv 128)) => do
      v_10268 <- evaluateAddress v_3337;
      v_10269 <- load v_10268 16;
      setRegister (lhs.of_reg v_3338) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_double_to_int32_truncate (extract v_10269 0 64)) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_double_to_int32_truncate (extract v_10269 64 128)) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_double_to_int32_truncate (extract v_10269 128 192)) (_(_)_MINT-WRAPPER-SYNTAX cvt_double_to_int32_truncate (extract v_10269 192 256)))));
      pure ()
    pat_end;
    pattern fun (v_3337 : Mem) (v_3338 : reg (bv 128)) => do
      v_10282 <- evaluateAddress v_3337;
      v_10283 <- load v_10282 32;
      setRegister (lhs.of_reg v_3338) (concat (expression.bv_nat 64 0) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_double_to_int32_truncate (extract v_10283 0 64)) (_(_)_MINT-WRAPPER-SYNTAX cvt_double_to_int32_truncate (extract v_10283 64 128))));
      pure ()
    pat_end;
    pattern fun (v_3337 : Mem) (v_3338 : reg (bv 128)) => do
      v_10291 <- evaluateAddress v_3337;
      v_10292 <- load v_10291 32;
      setRegister (lhs.of_reg v_3338) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_double_to_int32_truncate (extract v_10292 0 64)) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_double_to_int32_truncate (extract v_10292 64 128)) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_double_to_int32_truncate (extract v_10292 128 192)) (_(_)_MINT-WRAPPER-SYNTAX cvt_double_to_int32_truncate (extract v_10292 192 256)))));
      pure ()
    pat_end
