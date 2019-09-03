def roundps1 : instruction :=
  definst "roundps" $ do
    pattern fun (v_2818 : imm int) (v_2821 : reg (bv 128)) (v_2822 : reg (bv 128)) => do
      v_5768 <- getRegister v_2821;
      v_5770 <- eval (handleImmediateWithSignExtend v_2818 8 8);
      setRegister (lhs.of_reg v_2822) (concat (_(_,_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_rm (extract v_5768 0 32) v_5770) (concat (_(_,_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_rm (extract v_5768 32 64) v_5770) (concat (_(_,_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_rm (extract v_5768 64 96) v_5770) (_(_,_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_rm (extract v_5768 96 128) v_5770))));
      pure ()
    pat_end;
    pattern fun (v_2813 : imm int) (v_2814 : Mem) (v_2817 : reg (bv 128)) => do
      v_12961 <- evaluateAddress v_2814;
      v_12962 <- load v_12961 16;
      v_12964 <- eval (handleImmediateWithSignExtend v_2813 8 8);
      setRegister (lhs.of_reg v_2817) (concat (_(_,_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_rm (extract v_12962 0 32) v_12964) (concat (_(_,_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_rm (extract v_12962 32 64) v_12964) (concat (_(_,_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_rm (extract v_12962 64 96) v_12964) (_(_,_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_rm (extract v_12962 96 128) v_12964))));
      pure ()
    pat_end
