def vroundsd1 : instruction :=
  definst "vroundsd" $ do
    pattern fun (v_2919 : imm int) (v_2916 : reg (bv 128)) (v_2917 : reg (bv 128)) (v_2918 : reg (bv 128)) => do
      v_6726 <- getRegister v_2917;
      v_6728 <- getRegister v_2916;
      setRegister (lhs.of_reg v_2918) (concat (extract v_6726 0 64) (_(_,_)_MINT-WRAPPER-SYNTAX cvt_double_to_int64_rm (extract v_6728 64 128) (handleImmediateWithSignExtend v_2919 8 8)));
      pure ()
    pat_end;
    pattern fun (v_2912 : imm int) (v_2909 : Mem) (v_2910 : reg (bv 128)) (v_2911 : reg (bv 128)) => do
      v_12716 <- getRegister v_2910;
      v_12718 <- evaluateAddress v_2909;
      v_12719 <- load v_12718 8;
      setRegister (lhs.of_reg v_2911) (concat (extract v_12716 0 64) (_(_,_)_MINT-WRAPPER-SYNTAX cvt_double_to_int64_rm v_12719 (handleImmediateWithSignExtend v_2912 8 8)));
      pure ()
    pat_end
