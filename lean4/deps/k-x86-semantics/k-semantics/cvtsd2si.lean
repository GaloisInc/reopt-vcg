def cvtsd2si1 : instruction :=
  definst "cvtsd2si" $ do
    pattern fun (v_2591 : reg (bv 128)) (v_2590 : reg (bv 32)) => do
      v_4189 <- getRegister v_2591;
      setRegister (lhs.of_reg v_2590) (_(_)_MINT-WRAPPER-SYNTAX cvt_double_to_int32_truncate (extract v_4189 64 128));
      pure ()
    pat_end;
    pattern fun (v_2600 : reg (bv 128)) (v_2598 : reg (bv 64)) => do
      v_4197 <- getRegister v_2600;
      setRegister (lhs.of_reg v_2598) (_(_)_MINT-WRAPPER-SYNTAX cvt_double_to_int64_truncate (extract v_4197 64 128));
      pure ()
    pat_end;
    pattern fun (v_2585 : Mem) (v_2586 : reg (bv 32)) => do
      v_7906 <- evaluateAddress v_2585;
      v_7907 <- load v_7906 8;
      setRegister (lhs.of_reg v_2586) (_(_)_MINT-WRAPPER-SYNTAX cvt_double_to_int32_truncate v_7907);
      pure ()
    pat_end;
    pattern fun (v_2594 : Mem) (v_2595 : reg (bv 64)) => do
      v_7910 <- evaluateAddress v_2594;
      v_7911 <- load v_7910 8;
      setRegister (lhs.of_reg v_2595) (_(_)_MINT-WRAPPER-SYNTAX cvt_double_to_int64_truncate v_7911);
      pure ()
    pat_end
