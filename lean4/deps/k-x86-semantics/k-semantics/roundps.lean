def roundps1 : instruction :=
  definst "roundps" $ do
    pattern fun (v_2909 : imm int) (v_2912 : reg (bv 128)) (v_2913 : reg (bv 128)) => do
      v_5218 <- getRegister v_2912;
      v_5220 <- eval (handleImmediateWithSignExtend v_2909 8 8);
      setRegister (lhs.of_reg v_2913) (concat (_(_,_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_rm (extract v_5218 0 32) v_5220) (concat (_(_,_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_rm (extract v_5218 32 64) v_5220) (concat (_(_,_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_rm (extract v_5218 64 96) v_5220) (_(_,_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_rm (extract v_5218 96 128) v_5220))));
      pure ()
    pat_end;
    pattern fun (v_2904 : imm int) (v_2905 : Mem) (v_2908 : reg (bv 128)) => do
      v_10524 <- evaluateAddress v_2905;
      v_10525 <- load v_10524 16;
      v_10527 <- eval (handleImmediateWithSignExtend v_2904 8 8);
      setRegister (lhs.of_reg v_2908) (concat (_(_,_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_rm (extract v_10525 0 32) v_10527) (concat (_(_,_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_rm (extract v_10525 32 64) v_10527) (concat (_(_,_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_rm (extract v_10525 64 96) v_10527) (_(_,_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_rm (extract v_10525 96 128) v_10527))));
      pure ()
    pat_end
