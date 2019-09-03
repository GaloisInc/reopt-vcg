def vcvttps2dq1 : instruction :=
  definst "vcvttps2dq" $ do
    pattern fun (v_3292 : reg (bv 128)) (v_3293 : reg (bv 128)) => do
      v_6348 <- getRegister v_3292;
      setRegister (lhs.of_reg v_3293) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_truncate (extract v_6348 0 32)) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_truncate (extract v_6348 32 64)) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_truncate (extract v_6348 64 96)) (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_truncate (extract v_6348 96 128)))));
      pure ()
    pat_end;
    pattern fun (v_3299 : reg (bv 256)) (v_3300 : reg (bv 256)) => do
      v_6365 <- getRegister v_3299;
      setRegister (lhs.of_reg v_3300) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_truncate (extract v_6365 0 32)) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_truncate (extract v_6365 32 64)) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_truncate (extract v_6365 64 96)) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_truncate (extract v_6365 96 128)) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_truncate (extract v_6365 128 160)) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_truncate (extract v_6365 160 192)) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_truncate (extract v_6365 192 224)) (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_truncate (extract v_6365 224 256)))))))));
      pure ()
    pat_end;
    pattern fun (v_3285 : Mem) (v_3288 : reg (bv 128)) => do
      v_10543 <- evaluateAddress v_3285;
      v_10544 <- load v_10543 16;
      setRegister (lhs.of_reg v_3288) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_truncate (extract v_10544 0 32)) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_truncate (extract v_10544 32 64)) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_truncate (extract v_10544 64 96)) (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_truncate (extract v_10544 96 128)))));
      pure ()
    pat_end;
    pattern fun (v_3294 : Mem) (v_3295 : reg (bv 256)) => do
      v_10557 <- evaluateAddress v_3294;
      v_10558 <- load v_10557 32;
      setRegister (lhs.of_reg v_3295) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_truncate (extract v_10558 0 32)) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_truncate (extract v_10558 32 64)) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_truncate (extract v_10558 64 96)) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_truncate (extract v_10558 96 128)) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_truncate (extract v_10558 128 160)) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_truncate (extract v_10558 160 192)) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_truncate (extract v_10558 192 224)) (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_truncate (extract v_10558 224 256)))))))));
      pure ()
    pat_end
