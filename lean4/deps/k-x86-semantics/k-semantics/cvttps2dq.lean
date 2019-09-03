def cvttps2dq1 : instruction :=
  definst "cvttps2dq" $ do
    pattern fun (v_2624 : reg (bv 128)) (v_2625 : reg (bv 128)) => do
      v_4297 <- getRegister v_2624;
      setRegister (lhs.of_reg v_2625) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_truncate (extract v_4297 0 32)) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_truncate (extract v_4297 32 64)) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_truncate (extract v_4297 64 96)) (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_truncate (extract v_4297 96 128)))));
      pure ()
    pat_end;
    pattern fun (v_2620 : Mem) (v_2621 : reg (bv 128)) => do
      v_8207 <- evaluateAddress v_2620;
      v_8208 <- load v_8207 16;
      setRegister (lhs.of_reg v_2621) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_truncate (extract v_8208 0 32)) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_truncate (extract v_8208 32 64)) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_truncate (extract v_8208 64 96)) (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_truncate (extract v_8208 96 128)))));
      pure ()
    pat_end
