def cvttps2dq1 : instruction :=
  definst "cvttps2dq" $ do
    pattern fun (v_2715 : reg (bv 128)) (v_2716 : reg (bv 128)) => do
      v_4328 <- getRegister v_2715;
      setRegister (lhs.of_reg v_2716) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_truncate (extract v_4328 0 32)) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_truncate (extract v_4328 32 64)) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_truncate (extract v_4328 64 96)) (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_truncate (extract v_4328 96 128)))));
      pure ()
    pat_end;
    pattern fun (v_2711 : Mem) (v_2712 : reg (bv 128)) => do
      v_7995 <- evaluateAddress v_2711;
      v_7996 <- load v_7995 16;
      setRegister (lhs.of_reg v_2712) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_truncate (extract v_7996 0 32)) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_truncate (extract v_7996 32 64)) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_truncate (extract v_7996 64 96)) (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_truncate (extract v_7996 96 128)))));
      pure ()
    pat_end
