def vcvttss2si1 : instruction :=
  definst "vcvttss2si" $ do
    pattern fun (v_3420 : reg (bv 128)) (v_3419 : reg (bv 32)) => do
      v_6359 <- getRegister v_3420;
      setRegister (lhs.of_reg v_3419) (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_truncate (extract v_6359 96 128));
      pure ()
    pat_end;
    pattern fun (v_3429 : reg (bv 128)) (v_3425 : reg (bv 64)) => do
      v_6367 <- getRegister v_3429;
      setRegister (lhs.of_reg v_3425) (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int64_truncate (extract v_6367 96 128));
      pure ()
    pat_end;
    pattern fun (v_3412 : Mem) (v_3415 : reg (bv 32)) => do
      v_10380 <- evaluateAddress v_3412;
      v_10381 <- load v_10380 4;
      setRegister (lhs.of_reg v_3415) (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_truncate v_10381);
      pure ()
    pat_end;
    pattern fun (v_3421 : Mem) (v_3422 : reg (bv 64)) => do
      v_10384 <- evaluateAddress v_3421;
      v_10385 <- load v_10384 4;
      setRegister (lhs.of_reg v_3422) (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int64_truncate v_10385);
      pure ()
    pat_end
