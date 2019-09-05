def cvttsd2si1 : instruction :=
  definst "cvttsd2si" $ do
    pattern fun (v_2699 : reg (bv 128)) (v_2698 : reg (bv 32)) => do
      v_4324 <- getRegister v_2699;
      setRegister (lhs.of_reg v_2698) (_(_)_MINT-WRAPPER-SYNTAX cvt_double_to_int32_truncate (extract v_4324 64 128));
      pure ()
    pat_end;
    pattern fun (v_2708 : reg (bv 128)) (v_2706 : reg (bv 64)) => do
      v_4332 <- getRegister v_2708;
      setRegister (lhs.of_reg v_2706) (_(_)_MINT-WRAPPER-SYNTAX cvt_double_to_int64_truncate (extract v_4332 64 128));
      pure ()
    pat_end;
    pattern fun (v_2693 : Mem) (v_2694 : reg (bv 32)) => do
      v_7999 <- evaluateAddress v_2693;
      v_8000 <- load v_7999 8;
      setRegister (lhs.of_reg v_2694) (_(_)_MINT-WRAPPER-SYNTAX cvt_double_to_int32_truncate v_8000);
      pure ()
    pat_end;
    pattern fun (v_2702 : Mem) (v_2703 : reg (bv 64)) => do
      v_8003 <- evaluateAddress v_2702;
      v_8004 <- load v_8003 8;
      setRegister (lhs.of_reg v_2703) (_(_)_MINT-WRAPPER-SYNTAX cvt_double_to_int64_truncate v_8004);
      pure ()
    pat_end
