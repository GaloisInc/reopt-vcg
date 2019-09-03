def vroundss1 : instruction :=
  definst "vroundss" $ do
    pattern fun (v_2875 : imm int) (v_2876 : reg (bv 128)) (v_2877 : reg (bv 128)) (v_2878 : reg (bv 128)) => do
      v_6769 <- getRegister v_2877;
      v_6771 <- getRegister v_2876;
      setRegister (lhs.of_reg v_2878) (concat (extract v_6769 0 96) (_(_,_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_rm (extract v_6771 96 128) (handleImmediateWithSignExtend v_2875 8 8)));
      pure ()
    pat_end;
    pattern fun (v_2869 : imm int) (v_2870 : Mem) (v_2871 : reg (bv 128)) (v_2872 : reg (bv 128)) => do
      v_13126 <- getRegister v_2871;
      v_13128 <- evaluateAddress v_2870;
      v_13129 <- load v_13128 4;
      setRegister (lhs.of_reg v_2872) (concat (extract v_13126 0 96) (_(_,_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_rm v_13129 (handleImmediateWithSignExtend v_2869 8 8)));
      pure ()
    pat_end
