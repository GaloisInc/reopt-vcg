def vcvtsd2si1 : instruction :=
  definst "vcvtsd2si" $ do
    pattern fun (v_3147 : reg (bv 128)) (v_3144 : reg (bv 32)) => do
      v_6199 <- getRegister v_3147;
      setRegister (lhs.of_reg v_3144) (_(_)_MINT-WRAPPER-SYNTAX cvt_double_to_int32_truncate (extract v_6199 64 128));
      pure ()
    pat_end;
    pattern fun (v_3156 : reg (bv 128)) (v_3153 : reg (bv 64)) => do
      v_6207 <- getRegister v_3156;
      setRegister (lhs.of_reg v_3153) (_(_)_MINT-WRAPPER-SYNTAX cvt_double_to_int64_truncate (extract v_6207 64 128));
      pure ()
    pat_end;
    pattern fun (v_3139 : Mem) (v_3140 : reg (bv 32)) => do
      v_10425 <- evaluateAddress v_3139;
      v_10426 <- load v_10425 8;
      setRegister (lhs.of_reg v_3140) (_(_)_MINT-WRAPPER-SYNTAX cvt_double_to_int32_truncate v_10426);
      pure ()
    pat_end;
    pattern fun (v_3148 : Mem) (v_3149 : reg (bv 64)) => do
      v_10429 <- evaluateAddress v_3148;
      v_10430 <- load v_10429 8;
      setRegister (lhs.of_reg v_3149) (_(_)_MINT-WRAPPER-SYNTAX cvt_double_to_int64_truncate v_10430);
      pure ()
    pat_end
