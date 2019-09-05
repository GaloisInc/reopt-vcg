def cvtps2dq1 : instruction :=
  definst "cvtps2dq" $ do
    pattern fun (v_2572 : reg (bv 128)) (v_2573 : reg (bv 128)) => do
      v_4157 <- getRegister v_2572;
      setRegister (lhs.of_reg v_2573) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_truncate (extract v_4157 0 32)) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_truncate (extract v_4157 32 64)) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_truncate (extract v_4157 64 96)) (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_truncate (extract v_4157 96 128)))));
      pure ()
    pat_end;
    pattern fun (v_2567 : Mem) (v_2568 : reg (bv 128)) => do
      v_7880 <- evaluateAddress v_2567;
      v_7881 <- load v_7880 16;
      setRegister (lhs.of_reg v_2568) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_truncate (extract v_7881 0 32)) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_truncate (extract v_7881 32 64)) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_truncate (extract v_7881 64 96)) (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_truncate (extract v_7881 96 128)))));
      pure ()
    pat_end
