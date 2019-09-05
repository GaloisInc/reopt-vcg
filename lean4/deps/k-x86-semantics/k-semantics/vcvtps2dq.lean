def vcvtps2dq1 : instruction :=
  definst "vcvtps2dq" $ do
    pattern fun (v_3152 : reg (bv 128)) (v_3153 : reg (bv 128)) => do
      v_5958 <- getRegister v_3152;
      setRegister (lhs.of_reg v_3153) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_truncate (extract v_5958 0 32)) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_truncate (extract v_5958 32 64)) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_truncate (extract v_5958 64 96)) (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_truncate (extract v_5958 96 128)))));
      pure ()
    pat_end;
    pattern fun (v_3160 : reg (bv 256)) (v_3161 : reg (bv 256)) => do
      v_5975 <- getRegister v_3160;
      setRegister (lhs.of_reg v_3161) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_truncate (extract v_5975 0 32)) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_truncate (extract v_5975 32 64)) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_truncate (extract v_5975 64 96)) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_truncate (extract v_5975 96 128)) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_truncate (extract v_5975 128 160)) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_truncate (extract v_5975 160 192)) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_truncate (extract v_5975 192 224)) (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_truncate (extract v_5975 224 256)))))))));
      pure ()
    pat_end;
    pattern fun (v_3147 : Mem) (v_3148 : reg (bv 128)) => do
      v_10111 <- evaluateAddress v_3147;
      v_10112 <- load v_10111 16;
      setRegister (lhs.of_reg v_3148) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_truncate (extract v_10112 0 32)) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_truncate (extract v_10112 32 64)) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_truncate (extract v_10112 64 96)) (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_truncate (extract v_10112 96 128)))));
      pure ()
    pat_end;
    pattern fun (v_3156 : Mem) (v_3157 : reg (bv 256)) => do
      v_10125 <- evaluateAddress v_3156;
      v_10126 <- load v_10125 32;
      setRegister (lhs.of_reg v_3157) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_truncate (extract v_10126 0 32)) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_truncate (extract v_10126 32 64)) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_truncate (extract v_10126 64 96)) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_truncate (extract v_10126 96 128)) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_truncate (extract v_10126 128 160)) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_truncate (extract v_10126 160 192)) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_truncate (extract v_10126 192 224)) (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_truncate (extract v_10126 224 256)))))))));
      pure ()
    pat_end
