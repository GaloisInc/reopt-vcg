def vroundps1 : instruction :=
  definst "vroundps" $ do
    pattern fun (v_2828 : imm int) (v_2830 : reg (bv 128)) (v_2831 : reg (bv 128)) => do
      v_6761 <- getRegister v_2830;
      v_6763 <- eval (handleImmediateWithSignExtend v_2828 8 8);
      setRegister (lhs.of_reg v_2831) (concat (_(_,_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_rm (extract v_6761 0 32) v_6763) (concat (_(_,_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_rm (extract v_6761 32 64) v_6763) (concat (_(_,_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_rm (extract v_6761 64 96) v_6763) (_(_,_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_rm (extract v_6761 96 128) v_6763))));
      pure ()
    pat_end;
    pattern fun (v_2839 : imm int) (v_2840 : reg (bv 256)) (v_2841 : reg (bv 256)) => do
      v_6780 <- getRegister v_2840;
      v_6782 <- eval (handleImmediateWithSignExtend v_2839 8 8);
      setRegister (lhs.of_reg v_2841) (concat (_(_,_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_rm (extract v_6780 0 32) v_6782) (concat (_(_,_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_rm (extract v_6780 32 64) v_6782) (concat (_(_,_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_rm (extract v_6780 64 96) v_6782) (concat (_(_,_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_rm (extract v_6780 96 128) v_6782) (concat (_(_,_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_rm (extract v_6780 128 160) v_6782) (concat (_(_,_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_rm (extract v_6780 160 192) v_6782) (concat (_(_,_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_rm (extract v_6780 192 224) v_6782) (_(_,_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_rm (extract v_6780 224 256) v_6782))))))));
      pure ()
    pat_end;
    pattern fun (v_2823 : imm int) (v_2824 : Mem) (v_2825 : reg (bv 128)) => do
      v_13001 <- evaluateAddress v_2824;
      v_13002 <- load v_13001 16;
      v_13004 <- eval (handleImmediateWithSignExtend v_2823 8 8);
      setRegister (lhs.of_reg v_2825) (concat (_(_,_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_rm (extract v_13002 0 32) v_13004) (concat (_(_,_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_rm (extract v_13002 32 64) v_13004) (concat (_(_,_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_rm (extract v_13002 64 96) v_13004) (_(_,_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_rm (extract v_13002 96 128) v_13004))));
      pure ()
    pat_end;
    pattern fun (v_2834 : imm int) (v_2835 : Mem) (v_2836 : reg (bv 256)) => do
      v_13016 <- evaluateAddress v_2835;
      v_13017 <- load v_13016 32;
      v_13019 <- eval (handleImmediateWithSignExtend v_2834 8 8);
      setRegister (lhs.of_reg v_2836) (concat (_(_,_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_rm (extract v_13017 0 32) v_13019) (concat (_(_,_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_rm (extract v_13017 32 64) v_13019) (concat (_(_,_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_rm (extract v_13017 64 96) v_13019) (concat (_(_,_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_rm (extract v_13017 96 128) v_13019) (concat (_(_,_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_rm (extract v_13017 128 160) v_13019) (concat (_(_,_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_rm (extract v_13017 160 192) v_13019) (concat (_(_,_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_rm (extract v_13017 192 224) v_13019) (_(_,_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_rm (extract v_13017 224 256) v_13019))))))));
      pure ()
    pat_end
