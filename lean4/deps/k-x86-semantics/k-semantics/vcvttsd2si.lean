def vcvttsd2si1 : instruction :=
  definst "vcvttsd2si" $ do
    pattern fun (v_3324 : reg (bv 128)) (v_3320 : reg (bv 32)) => do
      v_7081 <- getRegister v_3324;
      setRegister (lhs.of_reg v_3320) (_(_)_MINT-WRAPPER-SYNTAX cvt_double_to_int32_truncate (extract v_7081 64 128));
      pure ()
    pat_end;
    pattern fun (v_3333 : reg (bv 128)) (v_3329 : reg (bv 64)) => do
      v_7089 <- getRegister v_3333;
      setRegister (lhs.of_reg v_3329) (_(_)_MINT-WRAPPER-SYNTAX cvt_double_to_int64_truncate (extract v_7089 64 128));
      pure ()
    pat_end;
    pattern fun (v_3317 : Mem) (v_3316 : reg (bv 32)) => do
      v_12317 <- evaluateAddress v_3317;
      v_12318 <- load v_12317 8;
      setRegister (lhs.of_reg v_3316) (_(_)_MINT-WRAPPER-SYNTAX cvt_double_to_int32_truncate v_12318);
      pure ()
    pat_end;
    pattern fun (v_3325 : Mem) (v_3326 : reg (bv 64)) => do
      v_12321 <- evaluateAddress v_3325;
      v_12322 <- load v_12321 8;
      setRegister (lhs.of_reg v_3326) (_(_)_MINT-WRAPPER-SYNTAX cvt_double_to_int64_truncate v_12322);
      pure ()
    pat_end
