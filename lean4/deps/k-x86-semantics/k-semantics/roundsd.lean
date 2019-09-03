def roundsd1 : instruction :=
  definst "roundsd" $ do
    pattern fun (v_2829 : imm int) (v_2832 : reg (bv 128)) (v_2833 : reg (bv 128)) => do
      v_5787 <- getRegister v_2833;
      v_5789 <- getRegister v_2832;
      setRegister (lhs.of_reg v_2833) (concat (extract v_5787 0 64) (_(_,_)_MINT-WRAPPER-SYNTAX cvt_double_to_int64_rm (extract v_5789 64 128) (handleImmediateWithSignExtend v_2829 8 8)));
      pure ()
    pat_end;
    pattern fun (v_2824 : imm int) (v_2825 : Mem) (v_2828 : reg (bv 128)) => do
      v_12976 <- getRegister v_2828;
      v_12978 <- evaluateAddress v_2825;
      v_12979 <- load v_12978 8;
      setRegister (lhs.of_reg v_2828) (concat (extract v_12976 0 64) (_(_,_)_MINT-WRAPPER-SYNTAX cvt_double_to_int64_rm v_12979 (handleImmediateWithSignExtend v_2824 8 8)));
      pure ()
    pat_end
