def roundss1 : instruction :=
  definst "roundss" $ do
    pattern fun (v_2853 : imm int) (v_2855 : reg (bv 128)) (v_2856 : reg (bv 128)) => do
      v_5818 <- getRegister v_2856;
      v_5820 <- getRegister v_2855;
      setRegister (lhs.of_reg v_2856) (concat (extract v_5818 0 96) (_(_,_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_rm (extract v_5820 96 128) (handleImmediateWithSignExtend v_2853 8 8)));
      pure ()
    pat_end;
    pattern fun (v_2849 : imm int) (v_2848 : Mem) (v_2850 : reg (bv 128)) => do
      v_12908 <- getRegister v_2850;
      v_12910 <- evaluateAddress v_2848;
      v_12911 <- load v_12910 4;
      setRegister (lhs.of_reg v_2850) (concat (extract v_12908 0 96) (_(_,_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_rm v_12911 (handleImmediateWithSignExtend v_2849 8 8)));
      pure ()
    pat_end
