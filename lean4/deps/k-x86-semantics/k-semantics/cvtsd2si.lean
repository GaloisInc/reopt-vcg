def cvtsd2si1 : instruction :=
  definst "cvtsd2si" $ do
    pattern fun (v_2617 : reg (bv 128)) (v_2616 : reg (bv 32)) => do
      v_4210 <- getRegister v_2617;
      setRegister (lhs.of_reg v_2616) (_(_)_MINT-WRAPPER-SYNTAX cvt_double_to_int32_truncate (extract v_4210 64 128));
      pure ()
    pat_end;
    pattern fun (v_2625 : reg (bv 128)) (v_2626 : reg (bv 64)) => do
      v_4218 <- getRegister v_2625;
      setRegister (lhs.of_reg v_2626) (_(_)_MINT-WRAPPER-SYNTAX cvt_double_to_int64_truncate (extract v_4218 64 128));
      pure ()
    pat_end;
    pattern fun (v_2612 : Mem) (v_2613 : reg (bv 32)) => do
      v_7916 <- evaluateAddress v_2612;
      v_7917 <- load v_7916 8;
      setRegister (lhs.of_reg v_2613) (_(_)_MINT-WRAPPER-SYNTAX cvt_double_to_int32_truncate v_7917);
      pure ()
    pat_end;
    pattern fun (v_2621 : Mem) (v_2622 : reg (bv 64)) => do
      v_7920 <- evaluateAddress v_2621;
      v_7921 <- load v_7920 8;
      setRegister (lhs.of_reg v_2622) (_(_)_MINT-WRAPPER-SYNTAX cvt_double_to_int64_truncate v_7921);
      pure ()
    pat_end
