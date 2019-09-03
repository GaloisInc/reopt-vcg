def vcvtps2dq1 : instruction :=
  definst "vcvtps2dq" $ do
    pattern fun (v_3088 : reg (bv 128)) (v_3089 : reg (bv 128)) => do
      v_6036 <- getRegister v_3088;
      setRegister (lhs.of_reg v_3089) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_truncate (extract v_6036 0 32)) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_truncate (extract v_6036 32 64)) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_truncate (extract v_6036 64 96)) (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_truncate (extract v_6036 96 128)))));
      pure ()
    pat_end;
    pattern fun (v_3095 : reg (bv 256)) (v_3096 : reg (bv 256)) => do
      v_6053 <- getRegister v_3095;
      setRegister (lhs.of_reg v_3096) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_truncate (extract v_6053 0 32)) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_truncate (extract v_6053 32 64)) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_truncate (extract v_6053 64 96)) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_truncate (extract v_6053 96 128)) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_truncate (extract v_6053 128 160)) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_truncate (extract v_6053 160 192)) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_truncate (extract v_6053 192 224)) (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_truncate (extract v_6053 224 256)))))))));
      pure ()
    pat_end;
    pattern fun (v_3081 : Mem) (v_3084 : reg (bv 128)) => do
      v_10349 <- evaluateAddress v_3081;
      v_10350 <- load v_10349 16;
      setRegister (lhs.of_reg v_3084) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_truncate (extract v_10350 0 32)) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_truncate (extract v_10350 32 64)) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_truncate (extract v_10350 64 96)) (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_truncate (extract v_10350 96 128)))));
      pure ()
    pat_end;
    pattern fun (v_3090 : Mem) (v_3091 : reg (bv 256)) => do
      v_10363 <- evaluateAddress v_3090;
      v_10364 <- load v_10363 32;
      setRegister (lhs.of_reg v_3091) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_truncate (extract v_10364 0 32)) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_truncate (extract v_10364 32 64)) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_truncate (extract v_10364 64 96)) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_truncate (extract v_10364 96 128)) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_truncate (extract v_10364 128 160)) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_truncate (extract v_10364 160 192)) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_truncate (extract v_10364 192 224)) (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_truncate (extract v_10364 224 256)))))))));
      pure ()
    pat_end
