def cvttss2si1 : instruction :=
  definst "cvttss2si" $ do
    pattern fun (v_2717 : reg (bv 128)) (v_2716 : reg (bv 32)) => do
      v_4340 <- getRegister v_2717;
      setRegister (lhs.of_reg v_2716) (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_truncate (extract v_4340 96 128));
      pure ()
    pat_end;
    pattern fun (v_2726 : reg (bv 128)) (v_2724 : reg (bv 64)) => do
      v_4348 <- getRegister v_2726;
      setRegister (lhs.of_reg v_2724) (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int64_truncate (extract v_4348 96 128));
      pure ()
    pat_end;
    pattern fun (v_2711 : Mem) (v_2712 : reg (bv 32)) => do
      v_8007 <- evaluateAddress v_2711;
      v_8008 <- load v_8007 4;
      setRegister (lhs.of_reg v_2712) (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_truncate v_8008);
      pure ()
    pat_end;
    pattern fun (v_2720 : Mem) (v_2721 : reg (bv 64)) => do
      v_8011 <- evaluateAddress v_2720;
      v_8012 <- load v_8011 4;
      setRegister (lhs.of_reg v_2721) (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int64_truncate v_8012);
      pure ()
    pat_end
