def cvttsd2si1 : instruction :=
  definst "cvttsd2si" $ do
    pattern fun (v_2647 : reg (bv 128)) (v_2645 : reg (bv 32)) => do
      v_4336 <- getRegister v_2647;
      setRegister (lhs.of_reg v_2645) (_(_)_MINT-WRAPPER-SYNTAX cvt_double_to_int32_truncate (extract v_4336 64 128));
      pure ()
    pat_end;
    pattern fun (v_2656 : reg (bv 128)) (v_2654 : reg (bv 64)) => do
      v_4344 <- getRegister v_2656;
      setRegister (lhs.of_reg v_2654) (_(_)_MINT-WRAPPER-SYNTAX cvt_double_to_int64_truncate (extract v_4344 64 128));
      pure ()
    pat_end;
    pattern fun (v_2640 : Mem) (v_2641 : reg (bv 32)) => do
      v_8529 <- evaluateAddress v_2640;
      v_8530 <- load v_8529 8;
      setRegister (lhs.of_reg v_2641) (_(_)_MINT-WRAPPER-SYNTAX cvt_double_to_int32_truncate v_8530);
      pure ()
    pat_end;
    pattern fun (v_2649 : Mem) (v_2650 : reg (bv 64)) => do
      v_8533 <- evaluateAddress v_2649;
      v_8534 <- load v_8533 8;
      setRegister (lhs.of_reg v_2650) (_(_)_MINT-WRAPPER-SYNTAX cvt_double_to_int64_truncate v_8534);
      pure ()
    pat_end
