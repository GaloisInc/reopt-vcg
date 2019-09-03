def cvtss2si1 : instruction :=
  definst "cvtss2si" $ do
    pattern fun (v_2611 : reg (bv 128)) (v_2609 : reg (bv 32)) => do
      v_4291 <- getRegister v_2611;
      setRegister (lhs.of_reg v_2609) (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_truncate (extract v_4291 96 128));
      pure ()
    pat_end;
    pattern fun (v_2620 : reg (bv 128)) (v_2618 : reg (bv 64)) => do
      v_4299 <- getRegister v_2620;
      setRegister (lhs.of_reg v_2618) (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int64_truncate (extract v_4299 96 128));
      pure ()
    pat_end;
    pattern fun (v_2604 : Mem) (v_2605 : reg (bv 32)) => do
      v_8498 <- evaluateAddress v_2604;
      v_8499 <- load v_8498 4;
      setRegister (lhs.of_reg v_2605) (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_truncate v_8499);
      pure ()
    pat_end;
    pattern fun (v_2613 : Mem) (v_2614 : reg (bv 64)) => do
      v_8502 <- evaluateAddress v_2613;
      v_8503 <- load v_8502 4;
      setRegister (lhs.of_reg v_2614) (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int64_truncate v_8503);
      pure ()
    pat_end
