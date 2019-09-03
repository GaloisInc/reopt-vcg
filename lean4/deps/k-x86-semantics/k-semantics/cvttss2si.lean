def cvttss2si1 : instruction :=
  definst "cvttss2si" $ do
    pattern fun (v_2651 : reg (bv 128)) (v_2652 : reg (bv 32)) => do
      v_4330 <- getRegister v_2651;
      setRegister (lhs.of_reg v_2652) (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_truncate (extract v_4330 96 128));
      pure ()
    pat_end;
    pattern fun (v_2661 : reg (bv 128)) (v_2660 : reg (bv 64)) => do
      v_4338 <- getRegister v_2661;
      setRegister (lhs.of_reg v_2660) (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int64_truncate (extract v_4338 96 128));
      pure ()
    pat_end;
    pattern fun (v_2647 : Mem) (v_2648 : reg (bv 32)) => do
      v_8229 <- evaluateAddress v_2647;
      v_8230 <- load v_8229 4;
      setRegister (lhs.of_reg v_2648) (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_truncate v_8230);
      pure ()
    pat_end;
    pattern fun (v_2656 : Mem) (v_2657 : reg (bv 64)) => do
      v_8233 <- evaluateAddress v_2656;
      v_8234 <- load v_8233 4;
      setRegister (lhs.of_reg v_2657) (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int64_truncate v_8234);
      pure ()
    pat_end
