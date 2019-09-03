def cvtps2dq1 : instruction :=
  definst "cvtps2dq" $ do
    pattern fun (v_2507 : reg (bv 128)) (v_2508 : reg (bv 128)) => do
      v_4147 <- getRegister v_2507;
      setRegister (lhs.of_reg v_2508) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_truncate (extract v_4147 0 32)) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_truncate (extract v_4147 32 64)) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_truncate (extract v_4147 64 96)) (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_truncate (extract v_4147 96 128)))));
      pure ()
    pat_end;
    pattern fun (v_2503 : Mem) (v_2504 : reg (bv 128)) => do
      v_8102 <- evaluateAddress v_2503;
      v_8103 <- load v_8102 16;
      setRegister (lhs.of_reg v_2504) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_truncate (extract v_8103 0 32)) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_truncate (extract v_8103 32 64)) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_truncate (extract v_8103 64 96)) (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_truncate (extract v_8103 96 128)))));
      pure ()
    pat_end
