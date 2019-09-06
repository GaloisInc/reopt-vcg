def vcvtss2si1 : instruction :=
  definst "vcvtss2si" $ do
    pattern fun (v_3352 : reg (bv 128)) (v_3351 : reg (bv 32)) => do
      v_6256 <- getRegister v_3352;
      setRegister (lhs.of_reg v_3351) (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_truncate (extract v_6256 96 128));
      pure ()
    pat_end;
    pattern fun (v_3361 : reg (bv 128)) (v_3357 : reg (bv 64)) => do
      v_6264 <- getRegister v_3361;
      setRegister (lhs.of_reg v_3357) (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int64_truncate (extract v_6264 96 128));
      pure ()
    pat_end;
    pattern fun (v_3344 : Mem) (v_3347 : reg (bv 32)) => do
      v_10278 <- evaluateAddress v_3344;
      v_10279 <- load v_10278 4;
      setRegister (lhs.of_reg v_3347) (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_truncate v_10279);
      pure ()
    pat_end;
    pattern fun (v_3353 : Mem) (v_3354 : reg (bv 64)) => do
      v_10282 <- evaluateAddress v_3353;
      v_10283 <- load v_10282 4;
      setRegister (lhs.of_reg v_3354) (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int64_truncate v_10283);
      pure ()
    pat_end
