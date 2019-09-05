def vroundpd1 : instruction :=
  definst "vroundpd" $ do
    pattern fun (v_2873 : imm int) (v_2871 : reg (bv 128)) (v_2872 : reg (bv 128)) => do
      v_6643 <- getRegister v_2871;
      v_6645 <- eval (handleImmediateWithSignExtend v_2873 8 8);
      setRegister (lhs.of_reg v_2872) (concat (_(_,_)_MINT-WRAPPER-SYNTAX cvt_double_to_int64_rm (extract v_6643 0 64) v_6645) (_(_,_)_MINT-WRAPPER-SYNTAX cvt_double_to_int64_rm (extract v_6643 64 128) v_6645));
      pure ()
    pat_end;
    pattern fun (v_2884 : imm int) (v_2882 : reg (bv 256)) (v_2883 : reg (bv 256)) => do
      v_6656 <- getRegister v_2882;
      v_6658 <- eval (handleImmediateWithSignExtend v_2884 8 8);
      setRegister (lhs.of_reg v_2883) (concat (_(_,_)_MINT-WRAPPER-SYNTAX cvt_double_to_int64_rm (extract v_6656 0 64) v_6658) (concat (_(_,_)_MINT-WRAPPER-SYNTAX cvt_double_to_int64_rm (extract v_6656 64 128) v_6658) (concat (_(_,_)_MINT-WRAPPER-SYNTAX cvt_double_to_int64_rm (extract v_6656 128 192) v_6658) (_(_,_)_MINT-WRAPPER-SYNTAX cvt_double_to_int64_rm (extract v_6656 192 256) v_6658))));
      pure ()
    pat_end;
    pattern fun (v_2867 : imm int) (v_2865 : Mem) (v_2866 : reg (bv 128)) => do
      v_12650 <- evaluateAddress v_2865;
      v_12651 <- load v_12650 16;
      v_12653 <- eval (handleImmediateWithSignExtend v_2867 8 8);
      setRegister (lhs.of_reg v_2866) (concat (_(_,_)_MINT-WRAPPER-SYNTAX cvt_double_to_int64_rm (extract v_12651 0 64) v_12653) (_(_,_)_MINT-WRAPPER-SYNTAX cvt_double_to_int64_rm (extract v_12651 64 128) v_12653));
      pure ()
    pat_end;
    pattern fun (v_2878 : imm int) (v_2876 : Mem) (v_2877 : reg (bv 256)) => do
      v_12659 <- evaluateAddress v_2876;
      v_12660 <- load v_12659 32;
      v_12662 <- eval (handleImmediateWithSignExtend v_2878 8 8);
      setRegister (lhs.of_reg v_2877) (concat (_(_,_)_MINT-WRAPPER-SYNTAX cvt_double_to_int64_rm (extract v_12660 0 64) v_12662) (concat (_(_,_)_MINT-WRAPPER-SYNTAX cvt_double_to_int64_rm (extract v_12660 64 128) v_12662) (concat (_(_,_)_MINT-WRAPPER-SYNTAX cvt_double_to_int64_rm (extract v_12660 128 192) v_12662) (_(_,_)_MINT-WRAPPER-SYNTAX cvt_double_to_int64_rm (extract v_12660 192 256) v_12662))));
      pure ()
    pat_end
