def vcvtsd2si1 : instruction :=
  definst "vcvtsd2si" $ do
    pattern fun (v_3160 : reg (bv 128)) (v_3156 : reg (bv 32)) => do
      v_6874 <- getRegister v_3160;
      setRegister (lhs.of_reg v_3156) (_(_)_MINT-WRAPPER-SYNTAX cvt_double_to_int32_truncate (extract v_6874 64 128));
      pure ()
    pat_end;
    pattern fun (v_3169 : reg (bv 128)) (v_3165 : reg (bv 64)) => do
      v_6882 <- getRegister v_3169;
      setRegister (lhs.of_reg v_3165) (_(_)_MINT-WRAPPER-SYNTAX cvt_double_to_int64_truncate (extract v_6882 64 128));
      pure ()
    pat_end;
    pattern fun (v_3153 : Mem) (v_3152 : reg (bv 32)) => do
      v_12147 <- evaluateAddress v_3153;
      v_12148 <- load v_12147 8;
      setRegister (lhs.of_reg v_3152) (_(_)_MINT-WRAPPER-SYNTAX cvt_double_to_int32_truncate v_12148);
      pure ()
    pat_end;
    pattern fun (v_3161 : Mem) (v_3162 : reg (bv 64)) => do
      v_12151 <- evaluateAddress v_3161;
      v_12152 <- load v_12151 8;
      setRegister (lhs.of_reg v_3162) (_(_)_MINT-WRAPPER-SYNTAX cvt_double_to_int64_truncate v_12152);
      pure ()
    pat_end
