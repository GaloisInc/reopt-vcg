def vcvtss2si1 : instruction :=
  definst "vcvtss2si" $ do
    pattern fun (v_3324 : reg (bv 128)) (v_3325 : reg (bv 32)) => do
      v_6229 <- getRegister v_3324;
      setRegister (lhs.of_reg v_3325) (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_truncate (extract v_6229 96 128));
      pure ()
    pat_end;
    pattern fun (v_3333 : reg (bv 128)) (v_3334 : reg (bv 64)) => do
      v_6237 <- getRegister v_3333;
      setRegister (lhs.of_reg v_3334) (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int64_truncate (extract v_6237 96 128));
      pure ()
    pat_end;
    pattern fun (v_3319 : Mem) (v_3320 : reg (bv 32)) => do
      v_10251 <- evaluateAddress v_3319;
      v_10252 <- load v_10251 4;
      setRegister (lhs.of_reg v_3320) (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_truncate v_10252);
      pure ()
    pat_end;
    pattern fun (v_3328 : Mem) (v_3329 : reg (bv 64)) => do
      v_10255 <- evaluateAddress v_3328;
      v_10256 <- load v_10255 4;
      setRegister (lhs.of_reg v_3329) (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int64_truncate v_10256);
      pure ()
    pat_end
