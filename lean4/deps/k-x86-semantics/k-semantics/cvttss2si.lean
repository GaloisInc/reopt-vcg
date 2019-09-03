def cvttss2si1 : instruction :=
  definst "cvttss2si" $ do
    pattern fun (v_2665 : reg (bv 128)) (v_2663 : reg (bv 32)) => do
      v_4352 <- getRegister v_2665;
      setRegister (lhs.of_reg v_2663) (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_truncate (extract v_4352 96 128));
      pure ()
    pat_end;
    pattern fun (v_2674 : reg (bv 128)) (v_2672 : reg (bv 64)) => do
      v_4360 <- getRegister v_2674;
      setRegister (lhs.of_reg v_2672) (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int64_truncate (extract v_4360 96 128));
      pure ()
    pat_end;
    pattern fun (v_2658 : Mem) (v_2659 : reg (bv 32)) => do
      v_8537 <- evaluateAddress v_2658;
      v_8538 <- load v_8537 4;
      setRegister (lhs.of_reg v_2659) (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_truncate v_8538);
      pure ()
    pat_end;
    pattern fun (v_2667 : Mem) (v_2668 : reg (bv 64)) => do
      v_8541 <- evaluateAddress v_2667;
      v_8542 <- load v_8541 4;
      setRegister (lhs.of_reg v_2668) (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int64_truncate v_8542);
      pure ()
    pat_end
