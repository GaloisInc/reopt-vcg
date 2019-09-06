def cvtps2dq1 : instruction :=
  definst "cvtps2dq" $ do
    pattern fun (v_2598 : reg (bv 128)) (v_2599 : reg (bv 128)) => do
      v_4178 <- getRegister v_2598;
      setRegister (lhs.of_reg v_2599) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_truncate (extract v_4178 0 32)) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_truncate (extract v_4178 32 64)) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_truncate (extract v_4178 64 96)) (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_truncate (extract v_4178 96 128)))));
      pure ()
    pat_end;
    pattern fun (v_2594 : Mem) (v_2595 : reg (bv 128)) => do
      v_7890 <- evaluateAddress v_2594;
      v_7891 <- load v_7890 16;
      setRegister (lhs.of_reg v_2595) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_truncate (extract v_7891 0 32)) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_truncate (extract v_7891 32 64)) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_truncate (extract v_7891 64 96)) (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_truncate (extract v_7891 96 128)))));
      pure ()
    pat_end
