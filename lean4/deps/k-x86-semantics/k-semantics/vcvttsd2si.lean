def vcvttsd2si1 : instruction :=
  definst "vcvttsd2si" $ do
    pattern fun (v_3402 : reg (bv 128)) (v_3401 : reg (bv 32)) => do
      v_6343 <- getRegister v_3402;
      setRegister (lhs.of_reg v_3401) (_(_)_MINT-WRAPPER-SYNTAX cvt_double_to_int32_truncate (extract v_6343 64 128));
      pure ()
    pat_end;
    pattern fun (v_3411 : reg (bv 128)) (v_3407 : reg (bv 64)) => do
      v_6351 <- getRegister v_3411;
      setRegister (lhs.of_reg v_3407) (_(_)_MINT-WRAPPER-SYNTAX cvt_double_to_int64_truncate (extract v_6351 64 128));
      pure ()
    pat_end;
    pattern fun (v_3394 : Mem) (v_3397 : reg (bv 32)) => do
      v_10372 <- evaluateAddress v_3394;
      v_10373 <- load v_10372 8;
      setRegister (lhs.of_reg v_3397) (_(_)_MINT-WRAPPER-SYNTAX cvt_double_to_int32_truncate v_10373);
      pure ()
    pat_end;
    pattern fun (v_3403 : Mem) (v_3404 : reg (bv 64)) => do
      v_10376 <- evaluateAddress v_3403;
      v_10377 <- load v_10376 8;
      setRegister (lhs.of_reg v_3404) (_(_)_MINT-WRAPPER-SYNTAX cvt_double_to_int64_truncate v_10377);
      pure ()
    pat_end
