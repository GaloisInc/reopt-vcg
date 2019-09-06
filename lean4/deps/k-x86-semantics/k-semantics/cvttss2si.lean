def cvttss2si1 : instruction :=
  definst "cvttss2si" $ do
    pattern fun (v_2743 : reg (bv 128)) (v_2742 : reg (bv 32)) => do
      v_4361 <- getRegister v_2743;
      setRegister (lhs.of_reg v_2742) (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_truncate (extract v_4361 96 128));
      pure ()
    pat_end;
    pattern fun (v_2751 : reg (bv 128)) (v_2752 : reg (bv 64)) => do
      v_4369 <- getRegister v_2751;
      setRegister (lhs.of_reg v_2752) (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int64_truncate (extract v_4369 96 128));
      pure ()
    pat_end;
    pattern fun (v_2738 : Mem) (v_2739 : reg (bv 32)) => do
      v_8017 <- evaluateAddress v_2738;
      v_8018 <- load v_8017 4;
      setRegister (lhs.of_reg v_2739) (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_truncate v_8018);
      pure ()
    pat_end;
    pattern fun (v_2747 : Mem) (v_2748 : reg (bv 64)) => do
      v_8021 <- evaluateAddress v_2747;
      v_8022 <- load v_8021 4;
      setRegister (lhs.of_reg v_2748) (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int64_truncate v_8022);
      pure ()
    pat_end
