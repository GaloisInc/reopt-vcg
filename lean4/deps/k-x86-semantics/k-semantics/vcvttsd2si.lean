def vcvttsd2si1 : instruction :=
  definst "vcvttsd2si" $ do
    pattern fun (v_3311 : reg (bv 128)) (v_3308 : reg (bv 32)) => do
      v_6394 <- getRegister v_3311;
      setRegister (lhs.of_reg v_3308) (_(_)_MINT-WRAPPER-SYNTAX cvt_double_to_int32_truncate (extract v_6394 64 128));
      pure ()
    pat_end;
    pattern fun (v_3320 : reg (bv 128)) (v_3317 : reg (bv 64)) => do
      v_6402 <- getRegister v_3320;
      setRegister (lhs.of_reg v_3317) (_(_)_MINT-WRAPPER-SYNTAX cvt_double_to_int64_truncate (extract v_6402 64 128));
      pure ()
    pat_end;
    pattern fun (v_3303 : Mem) (v_3304 : reg (bv 32)) => do
      v_10583 <- evaluateAddress v_3303;
      v_10584 <- load v_10583 8;
      setRegister (lhs.of_reg v_3304) (_(_)_MINT-WRAPPER-SYNTAX cvt_double_to_int32_truncate v_10584);
      pure ()
    pat_end;
    pattern fun (v_3312 : Mem) (v_3313 : reg (bv 64)) => do
      v_10587 <- evaluateAddress v_3312;
      v_10588 <- load v_10587 8;
      setRegister (lhs.of_reg v_3313) (_(_)_MINT-WRAPPER-SYNTAX cvt_double_to_int64_truncate v_10588);
      pure ()
    pat_end
