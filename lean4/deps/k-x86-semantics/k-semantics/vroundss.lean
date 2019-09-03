def vroundss1 : instruction :=
  definst "vroundss" $ do
    pattern fun (v_2864 : imm int) (v_2866 : reg (bv 128)) (v_2867 : reg (bv 128)) (v_2868 : reg (bv 128)) => do
      v_6826 <- getRegister v_2867;
      v_6828 <- getRegister v_2866;
      setRegister (lhs.of_reg v_2868) (concat (extract v_6826 0 96) (_(_,_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_rm (extract v_6828 96 128) (handleImmediateWithSignExtend v_2864 8 8)));
      pure ()
    pat_end;
    pattern fun (v_2858 : imm int) (v_2859 : Mem) (v_2860 : reg (bv 128)) (v_2861 : reg (bv 128)) => do
      v_13051 <- getRegister v_2860;
      v_13053 <- evaluateAddress v_2859;
      v_13054 <- load v_13053 4;
      setRegister (lhs.of_reg v_2861) (concat (extract v_13051 0 96) (_(_,_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_rm v_13054 (handleImmediateWithSignExtend v_2858 8 8)));
      pure ()
    pat_end
