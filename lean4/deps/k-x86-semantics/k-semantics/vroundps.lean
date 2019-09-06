def vroundps1 : instruction :=
  definst "vroundps" $ do
    pattern fun (v_2919 : imm int) (v_2921 : reg (bv 128)) (v_2922 : reg (bv 128)) => do
      v_6702 <- getRegister v_2921;
      v_6704 <- eval (handleImmediateWithSignExtend v_2919 8 8);
      setRegister (lhs.of_reg v_2922) (concat (_(_,_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_rm (extract v_6702 0 32) v_6704) (concat (_(_,_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_rm (extract v_6702 32 64) v_6704) (concat (_(_,_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_rm (extract v_6702 64 96) v_6704) (_(_,_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_rm (extract v_6702 96 128) v_6704))));
      pure ()
    pat_end;
    pattern fun (v_2930 : imm int) (v_2932 : reg (bv 256)) (v_2933 : reg (bv 256)) => do
      v_6721 <- getRegister v_2932;
      v_6723 <- eval (handleImmediateWithSignExtend v_2930 8 8);
      setRegister (lhs.of_reg v_2933) (concat (_(_,_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_rm (extract v_6721 0 32) v_6723) (concat (_(_,_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_rm (extract v_6721 32 64) v_6723) (concat (_(_,_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_rm (extract v_6721 64 96) v_6723) (concat (_(_,_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_rm (extract v_6721 96 128) v_6723) (concat (_(_,_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_rm (extract v_6721 128 160) v_6723) (concat (_(_,_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_rm (extract v_6721 160 192) v_6723) (concat (_(_,_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_rm (extract v_6721 192 224) v_6723) (_(_,_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_rm (extract v_6721 224 256) v_6723))))))));
      pure ()
    pat_end;
    pattern fun (v_2914 : imm int) (v_2915 : Mem) (v_2916 : reg (bv 128)) => do
      v_12701 <- evaluateAddress v_2915;
      v_12702 <- load v_12701 16;
      v_12704 <- eval (handleImmediateWithSignExtend v_2914 8 8);
      setRegister (lhs.of_reg v_2916) (concat (_(_,_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_rm (extract v_12702 0 32) v_12704) (concat (_(_,_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_rm (extract v_12702 32 64) v_12704) (concat (_(_,_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_rm (extract v_12702 64 96) v_12704) (_(_,_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_rm (extract v_12702 96 128) v_12704))));
      pure ()
    pat_end;
    pattern fun (v_2925 : imm int) (v_2926 : Mem) (v_2927 : reg (bv 256)) => do
      v_12716 <- evaluateAddress v_2926;
      v_12717 <- load v_12716 32;
      v_12719 <- eval (handleImmediateWithSignExtend v_2925 8 8);
      setRegister (lhs.of_reg v_2927) (concat (_(_,_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_rm (extract v_12717 0 32) v_12719) (concat (_(_,_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_rm (extract v_12717 32 64) v_12719) (concat (_(_,_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_rm (extract v_12717 64 96) v_12719) (concat (_(_,_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_rm (extract v_12717 96 128) v_12719) (concat (_(_,_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_rm (extract v_12717 128 160) v_12719) (concat (_(_,_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_rm (extract v_12717 160 192) v_12719) (concat (_(_,_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_rm (extract v_12717 192 224) v_12719) (_(_,_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_rm (extract v_12717 224 256) v_12719))))))));
      pure ()
    pat_end
