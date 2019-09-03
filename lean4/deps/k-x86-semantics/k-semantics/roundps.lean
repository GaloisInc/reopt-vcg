def roundps1 : instruction :=
  definst "roundps" $ do
    pattern fun (v_2831 : imm int) (v_2833 : reg (bv 128)) (v_2834 : reg (bv 128)) => do
      v_5786 <- getRegister v_2833;
      v_5788 <- eval (handleImmediateWithSignExtend v_2831 8 8);
      setRegister (lhs.of_reg v_2834) (concat (_(_,_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_rm (extract v_5786 0 32) v_5788) (concat (_(_,_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_rm (extract v_5786 32 64) v_5788) (concat (_(_,_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_rm (extract v_5786 64 96) v_5788) (_(_,_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_rm (extract v_5786 96 128) v_5788))));
      pure ()
    pat_end;
    pattern fun (v_2827 : imm int) (v_2826 : Mem) (v_2828 : reg (bv 128)) => do
      v_12885 <- evaluateAddress v_2826;
      v_12886 <- load v_12885 16;
      v_12888 <- eval (handleImmediateWithSignExtend v_2827 8 8);
      setRegister (lhs.of_reg v_2828) (concat (_(_,_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_rm (extract v_12886 0 32) v_12888) (concat (_(_,_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_rm (extract v_12886 32 64) v_12888) (concat (_(_,_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_rm (extract v_12886 64 96) v_12888) (_(_,_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_rm (extract v_12886 96 128) v_12888))));
      pure ()
    pat_end
