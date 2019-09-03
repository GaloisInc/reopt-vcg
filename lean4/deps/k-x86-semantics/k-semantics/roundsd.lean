def roundsd1 : instruction :=
  definst "roundsd" $ do
    pattern fun (v_2842 : imm int) (v_2844 : reg (bv 128)) (v_2845 : reg (bv 128)) => do
      v_5805 <- getRegister v_2845;
      v_5807 <- getRegister v_2844;
      setRegister (lhs.of_reg v_2845) (concat (extract v_5805 0 64) (_(_,_)_MINT-WRAPPER-SYNTAX cvt_double_to_int64_rm (extract v_5807 64 128) (handleImmediateWithSignExtend v_2842 8 8)));
      pure ()
    pat_end;
    pattern fun (v_2838 : imm int) (v_2837 : Mem) (v_2839 : reg (bv 128)) => do
      v_12900 <- getRegister v_2839;
      v_12902 <- evaluateAddress v_2837;
      v_12903 <- load v_12902 8;
      setRegister (lhs.of_reg v_2839) (concat (extract v_12900 0 64) (_(_,_)_MINT-WRAPPER-SYNTAX cvt_double_to_int64_rm v_12903 (handleImmediateWithSignExtend v_2838 8 8)));
      pure ()
    pat_end
