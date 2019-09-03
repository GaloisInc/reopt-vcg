def vroundps1 : instruction :=
  definst "vroundps" $ do
    pattern fun (v_2839 : imm int) (v_2840 : reg (bv 128)) (v_2841 : reg (bv 128)) => do
      v_6704 <- getRegister v_2840;
      v_6706 <- eval (handleImmediateWithSignExtend v_2839 8 8);
      setRegister (lhs.of_reg v_2841) (concat (_(_,_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_rm (extract v_6704 0 32) v_6706) (concat (_(_,_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_rm (extract v_6704 32 64) v_6706) (concat (_(_,_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_rm (extract v_6704 64 96) v_6706) (_(_,_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_rm (extract v_6704 96 128) v_6706))));
      pure ()
    pat_end;
    pattern fun (v_2850 : imm int) (v_2851 : reg (bv 256)) (v_2852 : reg (bv 256)) => do
      v_6723 <- getRegister v_2851;
      v_6725 <- eval (handleImmediateWithSignExtend v_2850 8 8);
      setRegister (lhs.of_reg v_2852) (concat (_(_,_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_rm (extract v_6723 0 32) v_6725) (concat (_(_,_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_rm (extract v_6723 32 64) v_6725) (concat (_(_,_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_rm (extract v_6723 64 96) v_6725) (concat (_(_,_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_rm (extract v_6723 96 128) v_6725) (concat (_(_,_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_rm (extract v_6723 128 160) v_6725) (concat (_(_,_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_rm (extract v_6723 160 192) v_6725) (concat (_(_,_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_rm (extract v_6723 192 224) v_6725) (_(_,_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_rm (extract v_6723 224 256) v_6725))))))));
      pure ()
    pat_end;
    pattern fun (v_2834 : imm int) (v_2835 : Mem) (v_2836 : reg (bv 128)) => do
      v_13076 <- evaluateAddress v_2835;
      v_13077 <- load v_13076 16;
      v_13079 <- eval (handleImmediateWithSignExtend v_2834 8 8);
      setRegister (lhs.of_reg v_2836) (concat (_(_,_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_rm (extract v_13077 0 32) v_13079) (concat (_(_,_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_rm (extract v_13077 32 64) v_13079) (concat (_(_,_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_rm (extract v_13077 64 96) v_13079) (_(_,_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_rm (extract v_13077 96 128) v_13079))));
      pure ()
    pat_end;
    pattern fun (v_2845 : imm int) (v_2846 : Mem) (v_2847 : reg (bv 256)) => do
      v_13091 <- evaluateAddress v_2846;
      v_13092 <- load v_13091 32;
      v_13094 <- eval (handleImmediateWithSignExtend v_2845 8 8);
      setRegister (lhs.of_reg v_2847) (concat (_(_,_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_rm (extract v_13092 0 32) v_13094) (concat (_(_,_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_rm (extract v_13092 32 64) v_13094) (concat (_(_,_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_rm (extract v_13092 64 96) v_13094) (concat (_(_,_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_rm (extract v_13092 96 128) v_13094) (concat (_(_,_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_rm (extract v_13092 128 160) v_13094) (concat (_(_,_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_rm (extract v_13092 160 192) v_13094) (concat (_(_,_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_rm (extract v_13092 192 224) v_13094) (_(_,_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_rm (extract v_13092 224 256) v_13094))))))));
      pure ()
    pat_end
