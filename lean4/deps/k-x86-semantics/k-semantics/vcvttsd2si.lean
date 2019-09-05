def vcvttsd2si1 : instruction :=
  definst "vcvttsd2si" $ do
    pattern fun (v_3374 : reg (bv 128)) (v_3375 : reg (bv 32)) => do
      v_6316 <- getRegister v_3374;
      setRegister (lhs.of_reg v_3375) (_(_)_MINT-WRAPPER-SYNTAX cvt_double_to_int32_truncate (extract v_6316 64 128));
      pure ()
    pat_end;
    pattern fun (v_3383 : reg (bv 128)) (v_3384 : reg (bv 64)) => do
      v_6324 <- getRegister v_3383;
      setRegister (lhs.of_reg v_3384) (_(_)_MINT-WRAPPER-SYNTAX cvt_double_to_int64_truncate (extract v_6324 64 128));
      pure ()
    pat_end;
    pattern fun (v_3369 : Mem) (v_3370 : reg (bv 32)) => do
      v_10345 <- evaluateAddress v_3369;
      v_10346 <- load v_10345 8;
      setRegister (lhs.of_reg v_3370) (_(_)_MINT-WRAPPER-SYNTAX cvt_double_to_int32_truncate v_10346);
      pure ()
    pat_end;
    pattern fun (v_3378 : Mem) (v_3379 : reg (bv 64)) => do
      v_10349 <- evaluateAddress v_3378;
      v_10350 <- load v_10349 8;
      setRegister (lhs.of_reg v_3379) (_(_)_MINT-WRAPPER-SYNTAX cvt_double_to_int64_truncate v_10350);
      pure ()
    pat_end
