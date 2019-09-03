def vroundsd1 : instruction :=
  definst "vroundsd" $ do
    pattern fun (v_2851 : imm int) (v_2853 : reg (bv 128)) (v_2854 : reg (bv 128)) (v_2855 : reg (bv 128)) => do
      v_6812 <- getRegister v_2854;
      v_6814 <- getRegister v_2853;
      setRegister (lhs.of_reg v_2855) (concat (extract v_6812 0 64) (_(_,_)_MINT-WRAPPER-SYNTAX cvt_double_to_int64_rm (extract v_6814 64 128) (handleImmediateWithSignExtend v_2851 8 8)));
      pure ()
    pat_end;
    pattern fun (v_2845 : imm int) (v_2846 : Mem) (v_2847 : reg (bv 128)) (v_2848 : reg (bv 128)) => do
      v_13043 <- getRegister v_2847;
      v_13045 <- evaluateAddress v_2846;
      v_13046 <- load v_13045 8;
      setRegister (lhs.of_reg v_2848) (concat (extract v_13043 0 64) (_(_,_)_MINT-WRAPPER-SYNTAX cvt_double_to_int64_rm v_13046 (handleImmediateWithSignExtend v_2845 8 8)));
      pure ()
    pat_end
