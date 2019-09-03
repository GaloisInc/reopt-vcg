def vroundsd1 : instruction :=
  definst "vroundsd" $ do
    pattern fun (v_2862 : imm int) (v_2863 : reg (bv 128)) (v_2864 : reg (bv 128)) (v_2865 : reg (bv 128)) => do
      v_6755 <- getRegister v_2864;
      v_6757 <- getRegister v_2863;
      setRegister (lhs.of_reg v_2865) (concat (extract v_6755 0 64) (_(_,_)_MINT-WRAPPER-SYNTAX cvt_double_to_int64_rm (extract v_6757 64 128) (handleImmediateWithSignExtend v_2862 8 8)));
      pure ()
    pat_end;
    pattern fun (v_2856 : imm int) (v_2857 : Mem) (v_2858 : reg (bv 128)) (v_2859 : reg (bv 128)) => do
      v_13118 <- getRegister v_2858;
      v_13120 <- evaluateAddress v_2857;
      v_13121 <- load v_13120 8;
      setRegister (lhs.of_reg v_2859) (concat (extract v_13118 0 64) (_(_,_)_MINT-WRAPPER-SYNTAX cvt_double_to_int64_rm v_13121 (handleImmediateWithSignExtend v_2856 8 8)));
      pure ()
    pat_end
