def vroundsd1 : instruction :=
  definst "vroundsd" $ do
    pattern fun (v_2942 : imm int) (v_2944 : reg (bv 128)) (v_2945 : reg (bv 128)) (v_2946 : reg (bv 128)) => do
      v_6753 <- getRegister v_2945;
      v_6755 <- getRegister v_2944;
      setRegister (lhs.of_reg v_2946) (concat (extract v_6753 0 64) (_(_,_)_MINT-WRAPPER-SYNTAX cvt_double_to_int64_rm (extract v_6755 64 128) (handleImmediateWithSignExtend v_2942 8 8)));
      pure ()
    pat_end;
    pattern fun (v_2936 : imm int) (v_2937 : Mem) (v_2938 : reg (bv 128)) (v_2939 : reg (bv 128)) => do
      v_12743 <- getRegister v_2938;
      v_12745 <- evaluateAddress v_2937;
      v_12746 <- load v_12745 8;
      setRegister (lhs.of_reg v_2939) (concat (extract v_12743 0 64) (_(_,_)_MINT-WRAPPER-SYNTAX cvt_double_to_int64_rm v_12746 (handleImmediateWithSignExtend v_2936 8 8)));
      pure ()
    pat_end
