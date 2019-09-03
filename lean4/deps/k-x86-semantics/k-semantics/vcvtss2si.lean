def vcvtss2si1 : instruction :=
  definst "vcvtss2si" $ do
    pattern fun (v_3261 : reg (bv 128)) (v_3258 : reg (bv 32)) => do
      v_6307 <- getRegister v_3261;
      setRegister (lhs.of_reg v_3258) (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_truncate (extract v_6307 96 128));
      pure ()
    pat_end;
    pattern fun (v_3270 : reg (bv 128)) (v_3267 : reg (bv 64)) => do
      v_6315 <- getRegister v_3270;
      setRegister (lhs.of_reg v_3267) (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int64_truncate (extract v_6315 96 128));
      pure ()
    pat_end;
    pattern fun (v_3253 : Mem) (v_3254 : reg (bv 32)) => do
      v_10489 <- evaluateAddress v_3253;
      v_10490 <- load v_10489 4;
      setRegister (lhs.of_reg v_3254) (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_truncate v_10490);
      pure ()
    pat_end;
    pattern fun (v_3262 : Mem) (v_3263 : reg (bv 64)) => do
      v_10493 <- evaluateAddress v_3262;
      v_10494 <- load v_10493 4;
      setRegister (lhs.of_reg v_3263) (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int64_truncate v_10494);
      pure ()
    pat_end
