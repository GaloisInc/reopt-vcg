def vcvtsd2si1 : instruction :=
  definst "vcvtsd2si" $ do
    pattern fun (v_3210 : reg (bv 128)) (v_3211 : reg (bv 32)) => do
      v_6121 <- getRegister v_3210;
      setRegister (lhs.of_reg v_3211) (_(_)_MINT-WRAPPER-SYNTAX cvt_double_to_int32_truncate (extract v_6121 64 128));
      pure ()
    pat_end;
    pattern fun (v_3219 : reg (bv 128)) (v_3220 : reg (bv 64)) => do
      v_6129 <- getRegister v_3219;
      setRegister (lhs.of_reg v_3220) (_(_)_MINT-WRAPPER-SYNTAX cvt_double_to_int64_truncate (extract v_6129 64 128));
      pure ()
    pat_end;
    pattern fun (v_3205 : Mem) (v_3206 : reg (bv 32)) => do
      v_10187 <- evaluateAddress v_3205;
      v_10188 <- load v_10187 8;
      setRegister (lhs.of_reg v_3206) (_(_)_MINT-WRAPPER-SYNTAX cvt_double_to_int32_truncate v_10188);
      pure ()
    pat_end;
    pattern fun (v_3214 : Mem) (v_3215 : reg (bv 64)) => do
      v_10191 <- evaluateAddress v_3214;
      v_10192 <- load v_10191 8;
      setRegister (lhs.of_reg v_3215) (_(_)_MINT-WRAPPER-SYNTAX cvt_double_to_int64_truncate v_10192);
      pure ()
    pat_end
