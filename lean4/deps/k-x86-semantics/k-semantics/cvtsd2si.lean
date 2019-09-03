def cvtsd2si1 : instruction :=
  definst "cvtsd2si" $ do
    pattern fun (v_2539 : reg (bv 128)) (v_2537 : reg (bv 32)) => do
      v_4189 <- getRegister v_2539;
      setRegister (lhs.of_reg v_2537) (_(_)_MINT-WRAPPER-SYNTAX cvt_double_to_int32_truncate (extract v_4189 64 128));
      pure ()
    pat_end;
    pattern fun (v_2548 : reg (bv 128)) (v_2546 : reg (bv 64)) => do
      v_4197 <- getRegister v_2548;
      setRegister (lhs.of_reg v_2546) (_(_)_MINT-WRAPPER-SYNTAX cvt_double_to_int64_truncate (extract v_4197 64 128));
      pure ()
    pat_end;
    pattern fun (v_2532 : Mem) (v_2533 : reg (bv 32)) => do
      v_8424 <- evaluateAddress v_2532;
      v_8425 <- load v_8424 8;
      setRegister (lhs.of_reg v_2533) (_(_)_MINT-WRAPPER-SYNTAX cvt_double_to_int32_truncate v_8425);
      pure ()
    pat_end;
    pattern fun (v_2541 : Mem) (v_2542 : reg (bv 64)) => do
      v_8428 <- evaluateAddress v_2541;
      v_8429 <- load v_8428 8;
      setRegister (lhs.of_reg v_2542) (_(_)_MINT-WRAPPER-SYNTAX cvt_double_to_int64_truncate v_8429);
      pure ()
    pat_end
