def cvtss2si1 : instruction :=
  definst "cvtss2si" $ do
    pattern fun (v_2663 : reg (bv 128)) (v_2662 : reg (bv 32)) => do
      v_4279 <- getRegister v_2663;
      setRegister (lhs.of_reg v_2662) (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_truncate (extract v_4279 96 128));
      pure ()
    pat_end;
    pattern fun (v_2672 : reg (bv 128)) (v_2670 : reg (bv 64)) => do
      v_4287 <- getRegister v_2672;
      setRegister (lhs.of_reg v_2670) (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int64_truncate (extract v_4287 96 128));
      pure ()
    pat_end;
    pattern fun (v_2657 : Mem) (v_2658 : reg (bv 32)) => do
      v_7968 <- evaluateAddress v_2657;
      v_7969 <- load v_7968 4;
      setRegister (lhs.of_reg v_2658) (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_truncate v_7969);
      pure ()
    pat_end;
    pattern fun (v_2666 : Mem) (v_2667 : reg (bv 64)) => do
      v_7972 <- evaluateAddress v_2666;
      v_7973 <- load v_7972 4;
      setRegister (lhs.of_reg v_2667) (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int64_truncate v_7973);
      pure ()
    pat_end
