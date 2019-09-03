def cvtsd2si1 : instruction :=
  definst "cvtsd2si" $ do
    pattern fun (v_2525 : reg (bv 128)) (v_2526 : reg (bv 32)) => do
      v_4179 <- getRegister v_2525;
      setRegister (lhs.of_reg v_2526) (_(_)_MINT-WRAPPER-SYNTAX cvt_double_to_int32_truncate (extract v_4179 64 128));
      pure ()
    pat_end;
    pattern fun (v_2535 : reg (bv 128)) (v_2534 : reg (bv 64)) => do
      v_4187 <- getRegister v_2535;
      setRegister (lhs.of_reg v_2534) (_(_)_MINT-WRAPPER-SYNTAX cvt_double_to_int64_truncate (extract v_4187 64 128));
      pure ()
    pat_end;
    pattern fun (v_2521 : Mem) (v_2522 : reg (bv 32)) => do
      v_8128 <- evaluateAddress v_2521;
      v_8129 <- load v_8128 8;
      setRegister (lhs.of_reg v_2522) (_(_)_MINT-WRAPPER-SYNTAX cvt_double_to_int32_truncate v_8129);
      pure ()
    pat_end;
    pattern fun (v_2530 : Mem) (v_2531 : reg (bv 64)) => do
      v_8132 <- evaluateAddress v_2530;
      v_8133 <- load v_8132 8;
      setRegister (lhs.of_reg v_2531) (_(_)_MINT-WRAPPER-SYNTAX cvt_double_to_int64_truncate v_8133);
      pure ()
    pat_end
