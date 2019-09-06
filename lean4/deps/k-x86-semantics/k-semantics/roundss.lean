def roundss1 : instruction :=
  definst "roundss" $ do
    pattern fun (v_2931 : imm int) (v_2934 : reg (bv 128)) (v_2935 : reg (bv 128)) => do
      v_5250 <- getRegister v_2935;
      v_5252 <- getRegister v_2934;
      setRegister (lhs.of_reg v_2935) (concat (extract v_5250 0 96) (_(_,_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_rm (extract v_5252 96 128) (handleImmediateWithSignExtend v_2931 8 8)));
      pure ()
    pat_end;
    pattern fun (v_2926 : imm int) (v_2927 : Mem) (v_2930 : reg (bv 128)) => do
      v_10547 <- getRegister v_2930;
      v_10549 <- evaluateAddress v_2927;
      v_10550 <- load v_10549 4;
      setRegister (lhs.of_reg v_2930) (concat (extract v_10547 0 96) (_(_,_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_rm v_10550 (handleImmediateWithSignExtend v_2926 8 8)));
      pure ()
    pat_end
