def vcvttss2si1 : instruction :=
  definst "vcvttss2si" $ do
    pattern fun (v_3329 : reg (bv 128)) (v_3326 : reg (bv 32)) => do
      v_6410 <- getRegister v_3329;
      setRegister (lhs.of_reg v_3326) (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_truncate (extract v_6410 96 128));
      pure ()
    pat_end;
    pattern fun (v_3338 : reg (bv 128)) (v_3335 : reg (bv 64)) => do
      v_6418 <- getRegister v_3338;
      setRegister (lhs.of_reg v_3335) (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int64_truncate (extract v_6418 96 128));
      pure ()
    pat_end;
    pattern fun (v_3321 : Mem) (v_3322 : reg (bv 32)) => do
      v_10591 <- evaluateAddress v_3321;
      v_10592 <- load v_10591 4;
      setRegister (lhs.of_reg v_3322) (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_truncate v_10592);
      pure ()
    pat_end;
    pattern fun (v_3330 : Mem) (v_3331 : reg (bv 64)) => do
      v_10595 <- evaluateAddress v_3330;
      v_10596 <- load v_10595 4;
      setRegister (lhs.of_reg v_3331) (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int64_truncate v_10596);
      pure ()
    pat_end
