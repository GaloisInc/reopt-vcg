def vroundpd1 : instruction :=
  definst "vroundpd" $ do
    pattern fun (v_2806 : imm int) (v_2808 : reg (bv 128)) (v_2809 : reg (bv 128)) => do
      v_6729 <- getRegister v_2808;
      v_6731 <- eval (handleImmediateWithSignExtend v_2806 8 8);
      setRegister (lhs.of_reg v_2809) (concat (_(_,_)_MINT-WRAPPER-SYNTAX cvt_double_to_int64_rm (extract v_6729 0 64) v_6731) (_(_,_)_MINT-WRAPPER-SYNTAX cvt_double_to_int64_rm (extract v_6729 64 128) v_6731));
      pure ()
    pat_end;
    pattern fun (v_2817 : imm int) (v_2818 : reg (bv 256)) (v_2819 : reg (bv 256)) => do
      v_6742 <- getRegister v_2818;
      v_6744 <- eval (handleImmediateWithSignExtend v_2817 8 8);
      setRegister (lhs.of_reg v_2819) (concat (_(_,_)_MINT-WRAPPER-SYNTAX cvt_double_to_int64_rm (extract v_6742 0 64) v_6744) (concat (_(_,_)_MINT-WRAPPER-SYNTAX cvt_double_to_int64_rm (extract v_6742 64 128) v_6744) (concat (_(_,_)_MINT-WRAPPER-SYNTAX cvt_double_to_int64_rm (extract v_6742 128 192) v_6744) (_(_,_)_MINT-WRAPPER-SYNTAX cvt_double_to_int64_rm (extract v_6742 192 256) v_6744))));
      pure ()
    pat_end;
    pattern fun (v_2801 : imm int) (v_2802 : Mem) (v_2803 : reg (bv 128)) => do
      v_12977 <- evaluateAddress v_2802;
      v_12978 <- load v_12977 16;
      v_12980 <- eval (handleImmediateWithSignExtend v_2801 8 8);
      setRegister (lhs.of_reg v_2803) (concat (_(_,_)_MINT-WRAPPER-SYNTAX cvt_double_to_int64_rm (extract v_12978 0 64) v_12980) (_(_,_)_MINT-WRAPPER-SYNTAX cvt_double_to_int64_rm (extract v_12978 64 128) v_12980));
      pure ()
    pat_end;
    pattern fun (v_2812 : imm int) (v_2813 : Mem) (v_2814 : reg (bv 256)) => do
      v_12986 <- evaluateAddress v_2813;
      v_12987 <- load v_12986 32;
      v_12989 <- eval (handleImmediateWithSignExtend v_2812 8 8);
      setRegister (lhs.of_reg v_2814) (concat (_(_,_)_MINT-WRAPPER-SYNTAX cvt_double_to_int64_rm (extract v_12987 0 64) v_12989) (concat (_(_,_)_MINT-WRAPPER-SYNTAX cvt_double_to_int64_rm (extract v_12987 64 128) v_12989) (concat (_(_,_)_MINT-WRAPPER-SYNTAX cvt_double_to_int64_rm (extract v_12987 128 192) v_12989) (_(_,_)_MINT-WRAPPER-SYNTAX cvt_double_to_int64_rm (extract v_12987 192 256) v_12989))));
      pure ()
    pat_end
