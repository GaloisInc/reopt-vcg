def vcvtss2si1 : instruction :=
  definst "vcvtss2si" $ do
    pattern fun (v_3274 : reg (bv 128)) (v_3270 : reg (bv 32)) => do
      v_6994 <- getRegister v_3274;
      setRegister (lhs.of_reg v_3270) (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_truncate (extract v_6994 96 128));
      pure ()
    pat_end;
    pattern fun (v_3283 : reg (bv 128)) (v_3279 : reg (bv 64)) => do
      v_7002 <- getRegister v_3283;
      setRegister (lhs.of_reg v_3279) (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int64_truncate (extract v_7002 96 128));
      pure ()
    pat_end;
    pattern fun (v_3267 : Mem) (v_3266 : reg (bv 32)) => do
      v_12223 <- evaluateAddress v_3267;
      v_12224 <- load v_12223 4;
      setRegister (lhs.of_reg v_3266) (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_truncate v_12224);
      pure ()
    pat_end;
    pattern fun (v_3275 : Mem) (v_3276 : reg (bv 64)) => do
      v_12227 <- evaluateAddress v_3275;
      v_12228 <- load v_12227 4;
      setRegister (lhs.of_reg v_3276) (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int64_truncate v_12228);
      pure ()
    pat_end
