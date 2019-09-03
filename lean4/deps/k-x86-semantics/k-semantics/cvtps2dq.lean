def cvtps2dq1 : instruction :=
  definst "cvtps2dq" $ do
    pattern fun (v_2520 : reg (bv 128)) (v_2521 : reg (bv 128)) => do
      v_4145 <- getRegister v_2520;
      setRegister (lhs.of_reg v_2521) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_truncate (extract v_4145 0 32)) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_truncate (extract v_4145 32 64)) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_truncate (extract v_4145 64 96)) (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_truncate (extract v_4145 96 128)))));
      pure ()
    pat_end;
    pattern fun (v_2514 : Mem) (v_2516 : reg (bv 128)) => do
      v_8386 <- evaluateAddress v_2514;
      v_8387 <- load v_8386 16;
      setRegister (lhs.of_reg v_2516) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_truncate (extract v_8387 0 32)) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_truncate (extract v_8387 32 64)) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_truncate (extract v_8387 64 96)) (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_truncate (extract v_8387 96 128)))));
      pure ()
    pat_end
