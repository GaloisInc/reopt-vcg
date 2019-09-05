def vroundss1 : instruction :=
  definst "vroundss" $ do
    pattern fun (v_2932 : imm int) (v_2929 : reg (bv 128)) (v_2930 : reg (bv 128)) (v_2931 : reg (bv 128)) => do
      v_6740 <- getRegister v_2930;
      v_6742 <- getRegister v_2929;
      setRegister (lhs.of_reg v_2931) (concat (extract v_6740 0 96) (_(_,_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_rm (extract v_6742 96 128) (handleImmediateWithSignExtend v_2932 8 8)));
      pure ()
    pat_end;
    pattern fun (v_2925 : imm int) (v_2922 : Mem) (v_2923 : reg (bv 128)) (v_2924 : reg (bv 128)) => do
      v_12724 <- getRegister v_2923;
      v_12726 <- evaluateAddress v_2922;
      v_12727 <- load v_12726 4;
      setRegister (lhs.of_reg v_2924) (concat (extract v_12724 0 96) (_(_,_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_rm v_12727 (handleImmediateWithSignExtend v_2925 8 8)));
      pure ()
    pat_end
