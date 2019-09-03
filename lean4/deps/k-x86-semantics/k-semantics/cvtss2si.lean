def cvtss2si1 : instruction :=
  definst "cvtss2si" $ do
    pattern fun (v_2597 : reg (bv 128)) (v_2598 : reg (bv 32)) => do
      v_4269 <- getRegister v_2597;
      setRegister (lhs.of_reg v_2598) (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_truncate (extract v_4269 96 128));
      pure ()
    pat_end;
    pattern fun (v_2607 : reg (bv 128)) (v_2606 : reg (bv 64)) => do
      v_4277 <- getRegister v_2607;
      setRegister (lhs.of_reg v_2606) (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int64_truncate (extract v_4277 96 128));
      pure ()
    pat_end;
    pattern fun (v_2593 : Mem) (v_2594 : reg (bv 32)) => do
      v_8190 <- evaluateAddress v_2593;
      v_8191 <- load v_8190 4;
      setRegister (lhs.of_reg v_2594) (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_truncate v_8191);
      pure ()
    pat_end;
    pattern fun (v_2602 : Mem) (v_2603 : reg (bv 64)) => do
      v_8194 <- evaluateAddress v_2602;
      v_8195 <- load v_8194 4;
      setRegister (lhs.of_reg v_2603) (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int64_truncate v_8195);
      pure ()
    pat_end
