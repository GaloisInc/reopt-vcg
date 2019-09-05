def vcvttss2si1 : instruction :=
  definst "vcvttss2si" $ do
    pattern fun (v_3392 : reg (bv 128)) (v_3393 : reg (bv 32)) => do
      v_6332 <- getRegister v_3392;
      setRegister (lhs.of_reg v_3393) (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_truncate (extract v_6332 96 128));
      pure ()
    pat_end;
    pattern fun (v_3401 : reg (bv 128)) (v_3402 : reg (bv 64)) => do
      v_6340 <- getRegister v_3401;
      setRegister (lhs.of_reg v_3402) (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int64_truncate (extract v_6340 96 128));
      pure ()
    pat_end;
    pattern fun (v_3387 : Mem) (v_3388 : reg (bv 32)) => do
      v_10353 <- evaluateAddress v_3387;
      v_10354 <- load v_10353 4;
      setRegister (lhs.of_reg v_3388) (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_truncate v_10354);
      pure ()
    pat_end;
    pattern fun (v_3396 : Mem) (v_3397 : reg (bv 64)) => do
      v_10357 <- evaluateAddress v_3396;
      v_10358 <- load v_10357 4;
      setRegister (lhs.of_reg v_3397) (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int64_truncate v_10358);
      pure ()
    pat_end
