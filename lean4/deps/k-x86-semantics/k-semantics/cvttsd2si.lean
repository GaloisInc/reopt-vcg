def cvttsd2si1 : instruction :=
  definst "cvttsd2si" $ do
    pattern fun (v_2725 : reg (bv 128)) (v_2724 : reg (bv 32)) => do
      v_4345 <- getRegister v_2725;
      setRegister (lhs.of_reg v_2724) (_(_)_MINT-WRAPPER-SYNTAX cvt_double_to_int32_truncate (extract v_4345 64 128));
      pure ()
    pat_end;
    pattern fun (v_2733 : reg (bv 128)) (v_2734 : reg (bv 64)) => do
      v_4353 <- getRegister v_2733;
      setRegister (lhs.of_reg v_2734) (_(_)_MINT-WRAPPER-SYNTAX cvt_double_to_int64_truncate (extract v_4353 64 128));
      pure ()
    pat_end;
    pattern fun (v_2720 : Mem) (v_2721 : reg (bv 32)) => do
      v_8009 <- evaluateAddress v_2720;
      v_8010 <- load v_8009 8;
      setRegister (lhs.of_reg v_2721) (_(_)_MINT-WRAPPER-SYNTAX cvt_double_to_int32_truncate v_8010);
      pure ()
    pat_end;
    pattern fun (v_2729 : Mem) (v_2730 : reg (bv 64)) => do
      v_8013 <- evaluateAddress v_2729;
      v_8014 <- load v_8013 8;
      setRegister (lhs.of_reg v_2730) (_(_)_MINT-WRAPPER-SYNTAX cvt_double_to_int64_truncate v_8014);
      pure ()
    pat_end
