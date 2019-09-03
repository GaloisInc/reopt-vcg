def cvttsd2si1 : instruction :=
  definst "cvttsd2si" $ do
    pattern fun (v_2633 : reg (bv 128)) (v_2634 : reg (bv 32)) => do
      v_4314 <- getRegister v_2633;
      setRegister (lhs.of_reg v_2634) (_(_)_MINT-WRAPPER-SYNTAX cvt_double_to_int32_truncate (extract v_4314 64 128));
      pure ()
    pat_end;
    pattern fun (v_2643 : reg (bv 128)) (v_2642 : reg (bv 64)) => do
      v_4322 <- getRegister v_2643;
      setRegister (lhs.of_reg v_2642) (_(_)_MINT-WRAPPER-SYNTAX cvt_double_to_int64_truncate (extract v_4322 64 128));
      pure ()
    pat_end;
    pattern fun (v_2629 : Mem) (v_2630 : reg (bv 32)) => do
      v_8221 <- evaluateAddress v_2629;
      v_8222 <- load v_8221 8;
      setRegister (lhs.of_reg v_2630) (_(_)_MINT-WRAPPER-SYNTAX cvt_double_to_int32_truncate v_8222);
      pure ()
    pat_end;
    pattern fun (v_2638 : Mem) (v_2639 : reg (bv 64)) => do
      v_8225 <- evaluateAddress v_2638;
      v_8226 <- load v_8225 8;
      setRegister (lhs.of_reg v_2639) (_(_)_MINT-WRAPPER-SYNTAX cvt_double_to_int64_truncate v_8226);
      pure ()
    pat_end
