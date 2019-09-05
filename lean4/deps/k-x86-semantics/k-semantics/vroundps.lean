def vroundps1 : instruction :=
  definst "vroundps" $ do
    pattern fun (v_2895 : imm int) (v_2893 : reg (bv 128)) (v_2894 : reg (bv 128)) => do
      v_6675 <- getRegister v_2893;
      v_6677 <- eval (handleImmediateWithSignExtend v_2895 8 8);
      setRegister (lhs.of_reg v_2894) (concat (_(_,_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_rm (extract v_6675 0 32) v_6677) (concat (_(_,_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_rm (extract v_6675 32 64) v_6677) (concat (_(_,_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_rm (extract v_6675 64 96) v_6677) (_(_,_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_rm (extract v_6675 96 128) v_6677))));
      pure ()
    pat_end;
    pattern fun (v_2906 : imm int) (v_2904 : reg (bv 256)) (v_2905 : reg (bv 256)) => do
      v_6694 <- getRegister v_2904;
      v_6696 <- eval (handleImmediateWithSignExtend v_2906 8 8);
      setRegister (lhs.of_reg v_2905) (concat (_(_,_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_rm (extract v_6694 0 32) v_6696) (concat (_(_,_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_rm (extract v_6694 32 64) v_6696) (concat (_(_,_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_rm (extract v_6694 64 96) v_6696) (concat (_(_,_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_rm (extract v_6694 96 128) v_6696) (concat (_(_,_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_rm (extract v_6694 128 160) v_6696) (concat (_(_,_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_rm (extract v_6694 160 192) v_6696) (concat (_(_,_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_rm (extract v_6694 192 224) v_6696) (_(_,_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_rm (extract v_6694 224 256) v_6696))))))));
      pure ()
    pat_end;
    pattern fun (v_2889 : imm int) (v_2887 : Mem) (v_2888 : reg (bv 128)) => do
      v_12674 <- evaluateAddress v_2887;
      v_12675 <- load v_12674 16;
      v_12677 <- eval (handleImmediateWithSignExtend v_2889 8 8);
      setRegister (lhs.of_reg v_2888) (concat (_(_,_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_rm (extract v_12675 0 32) v_12677) (concat (_(_,_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_rm (extract v_12675 32 64) v_12677) (concat (_(_,_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_rm (extract v_12675 64 96) v_12677) (_(_,_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_rm (extract v_12675 96 128) v_12677))));
      pure ()
    pat_end;
    pattern fun (v_2900 : imm int) (v_2898 : Mem) (v_2899 : reg (bv 256)) => do
      v_12689 <- evaluateAddress v_2898;
      v_12690 <- load v_12689 32;
      v_12692 <- eval (handleImmediateWithSignExtend v_2900 8 8);
      setRegister (lhs.of_reg v_2899) (concat (_(_,_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_rm (extract v_12690 0 32) v_12692) (concat (_(_,_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_rm (extract v_12690 32 64) v_12692) (concat (_(_,_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_rm (extract v_12690 64 96) v_12692) (concat (_(_,_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_rm (extract v_12690 96 128) v_12692) (concat (_(_,_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_rm (extract v_12690 128 160) v_12692) (concat (_(_,_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_rm (extract v_12690 160 192) v_12692) (concat (_(_,_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_rm (extract v_12690 192 224) v_12692) (_(_,_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_rm (extract v_12690 224 256) v_12692))))))));
      pure ()
    pat_end
