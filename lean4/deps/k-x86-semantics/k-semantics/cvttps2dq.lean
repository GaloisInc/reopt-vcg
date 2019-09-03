def cvttps2dq1 : instruction :=
  definst "cvttps2dq" $ do
    pattern fun (v_2637 : reg (bv 128)) (v_2638 : reg (bv 128)) => do
      v_4319 <- getRegister v_2637;
      setRegister (lhs.of_reg v_2638) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_truncate (extract v_4319 0 32)) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_truncate (extract v_4319 32 64)) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_truncate (extract v_4319 64 96)) (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_truncate (extract v_4319 96 128)))));
      pure ()
    pat_end;
    pattern fun (v_2631 : Mem) (v_2633 : reg (bv 128)) => do
      v_8515 <- evaluateAddress v_2631;
      v_8516 <- load v_8515 16;
      setRegister (lhs.of_reg v_2633) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_truncate (extract v_8516 0 32)) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_truncate (extract v_8516 32 64)) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_truncate (extract v_8516 64 96)) (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_truncate (extract v_8516 96 128)))));
      pure ()
    pat_end
