def vcvttss2si1 : instruction :=
  definst "vcvttss2si" $ do
    pattern fun (v_3342 : reg (bv 128)) (v_3338 : reg (bv 32)) => do
      v_7097 <- getRegister v_3342;
      setRegister (lhs.of_reg v_3338) (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_truncate (extract v_7097 96 128));
      pure ()
    pat_end;
    pattern fun (v_3351 : reg (bv 128)) (v_3347 : reg (bv 64)) => do
      v_7105 <- getRegister v_3351;
      setRegister (lhs.of_reg v_3347) (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int64_truncate (extract v_7105 96 128));
      pure ()
    pat_end;
    pattern fun (v_3335 : Mem) (v_3334 : reg (bv 32)) => do
      v_12325 <- evaluateAddress v_3335;
      v_12326 <- load v_12325 4;
      setRegister (lhs.of_reg v_3334) (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_truncate v_12326);
      pure ()
    pat_end;
    pattern fun (v_3343 : Mem) (v_3344 : reg (bv 64)) => do
      v_12329 <- evaluateAddress v_3343;
      v_12330 <- load v_12329 4;
      setRegister (lhs.of_reg v_3344) (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int64_truncate v_12330);
      pure ()
    pat_end
