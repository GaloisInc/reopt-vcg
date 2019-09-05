def cvttps2dq1 : instruction :=
  definst "cvttps2dq" $ do
    pattern fun (v_2689 : reg (bv 128)) (v_2690 : reg (bv 128)) => do
      v_4307 <- getRegister v_2689;
      setRegister (lhs.of_reg v_2690) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_truncate (extract v_4307 0 32)) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_truncate (extract v_4307 32 64)) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_truncate (extract v_4307 64 96)) (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_truncate (extract v_4307 96 128)))));
      pure ()
    pat_end;
    pattern fun (v_2684 : Mem) (v_2685 : reg (bv 128)) => do
      v_7985 <- evaluateAddress v_2684;
      v_7986 <- load v_7985 16;
      setRegister (lhs.of_reg v_2685) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_truncate (extract v_7986 0 32)) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_truncate (extract v_7986 32 64)) (concat (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_truncate (extract v_7986 64 96)) (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_truncate (extract v_7986 96 128)))));
      pure ()
    pat_end
