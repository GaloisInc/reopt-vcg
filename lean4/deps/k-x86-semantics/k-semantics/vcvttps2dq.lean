def vcvttps2dq1 : instruction :=
  definst "vcvttps2dq" $ do
    pattern fun (v_3356 : reg (bv 128)) (v_3357 : reg (bv 128)) => do
      v_6270 <- getRegister v_3356;
      setRegister (lhs.of_reg v_3357) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_truncate (extract v_6270 0 32)) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_truncate (extract v_6270 32 64)) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_truncate (extract v_6270 64 96)) (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_truncate (extract v_6270 96 128)))));
      pure ()
    pat_end;
    pattern fun (v_3364 : reg (bv 256)) (v_3365 : reg (bv 256)) => do
      v_6287 <- getRegister v_3364;
      setRegister (lhs.of_reg v_3365) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_truncate (extract v_6287 0 32)) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_truncate (extract v_6287 32 64)) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_truncate (extract v_6287 64 96)) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_truncate (extract v_6287 96 128)) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_truncate (extract v_6287 128 160)) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_truncate (extract v_6287 160 192)) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_truncate (extract v_6287 192 224)) (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_truncate (extract v_6287 224 256)))))))));
      pure ()
    pat_end;
    pattern fun (v_3351 : Mem) (v_3352 : reg (bv 128)) => do
      v_10305 <- evaluateAddress v_3351;
      v_10306 <- load v_10305 16;
      setRegister (lhs.of_reg v_3352) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_truncate (extract v_10306 0 32)) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_truncate (extract v_10306 32 64)) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_truncate (extract v_10306 64 96)) (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_truncate (extract v_10306 96 128)))));
      pure ()
    pat_end;
    pattern fun (v_3360 : Mem) (v_3361 : reg (bv 256)) => do
      v_10319 <- evaluateAddress v_3360;
      v_10320 <- load v_10319 32;
      setRegister (lhs.of_reg v_3361) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_truncate (extract v_10320 0 32)) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_truncate (extract v_10320 32 64)) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_truncate (extract v_10320 64 96)) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_truncate (extract v_10320 96 128)) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_truncate (extract v_10320 128 160)) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_truncate (extract v_10320 160 192)) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_truncate (extract v_10320 192 224)) (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_truncate (extract v_10320 224 256)))))))));
      pure ()
    pat_end
