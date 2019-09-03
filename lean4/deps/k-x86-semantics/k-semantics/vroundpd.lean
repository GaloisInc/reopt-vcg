def vroundpd1 : instruction :=
  definst "vroundpd" $ do
    pattern fun (v_2817 : imm int) (v_2818 : reg (bv 128)) (v_2819 : reg (bv 128)) => do
      v_6672 <- getRegister v_2818;
      v_6674 <- eval (handleImmediateWithSignExtend v_2817 8 8);
      setRegister (lhs.of_reg v_2819) (concat (_(_,_)_MINT-WRAPPER-SYNTAX cvt_double_to_int64_rm (extract v_6672 0 64) v_6674) (_(_,_)_MINT-WRAPPER-SYNTAX cvt_double_to_int64_rm (extract v_6672 64 128) v_6674));
      pure ()
    pat_end;
    pattern fun (v_2828 : imm int) (v_2829 : reg (bv 256)) (v_2830 : reg (bv 256)) => do
      v_6685 <- getRegister v_2829;
      v_6687 <- eval (handleImmediateWithSignExtend v_2828 8 8);
      setRegister (lhs.of_reg v_2830) (concat (_(_,_)_MINT-WRAPPER-SYNTAX cvt_double_to_int64_rm (extract v_6685 0 64) v_6687) (concat (_(_,_)_MINT-WRAPPER-SYNTAX cvt_double_to_int64_rm (extract v_6685 64 128) v_6687) (concat (_(_,_)_MINT-WRAPPER-SYNTAX cvt_double_to_int64_rm (extract v_6685 128 192) v_6687) (_(_,_)_MINT-WRAPPER-SYNTAX cvt_double_to_int64_rm (extract v_6685 192 256) v_6687))));
      pure ()
    pat_end;
    pattern fun (v_2812 : imm int) (v_2813 : Mem) (v_2814 : reg (bv 128)) => do
      v_13052 <- evaluateAddress v_2813;
      v_13053 <- load v_13052 16;
      v_13055 <- eval (handleImmediateWithSignExtend v_2812 8 8);
      setRegister (lhs.of_reg v_2814) (concat (_(_,_)_MINT-WRAPPER-SYNTAX cvt_double_to_int64_rm (extract v_13053 0 64) v_13055) (_(_,_)_MINT-WRAPPER-SYNTAX cvt_double_to_int64_rm (extract v_13053 64 128) v_13055));
      pure ()
    pat_end;
    pattern fun (v_2823 : imm int) (v_2824 : Mem) (v_2825 : reg (bv 256)) => do
      v_13061 <- evaluateAddress v_2824;
      v_13062 <- load v_13061 32;
      v_13064 <- eval (handleImmediateWithSignExtend v_2823 8 8);
      setRegister (lhs.of_reg v_2825) (concat (_(_,_)_MINT-WRAPPER-SYNTAX cvt_double_to_int64_rm (extract v_13062 0 64) v_13064) (concat (_(_,_)_MINT-WRAPPER-SYNTAX cvt_double_to_int64_rm (extract v_13062 64 128) v_13064) (concat (_(_,_)_MINT-WRAPPER-SYNTAX cvt_double_to_int64_rm (extract v_13062 128 192) v_13064) (_(_,_)_MINT-WRAPPER-SYNTAX cvt_double_to_int64_rm (extract v_13062 192 256) v_13064))));
      pure ()
    pat_end
