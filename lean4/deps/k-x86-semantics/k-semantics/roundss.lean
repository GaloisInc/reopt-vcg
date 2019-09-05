def roundss1 : instruction :=
  definst "roundss" $ do
    pattern fun (v_2906 : imm int) (v_2908 : reg (bv 128)) (v_2909 : reg (bv 128)) => do
      v_5542 <- getRegister v_2909;
      v_5544 <- getRegister v_2908;
      setRegister (lhs.of_reg v_2909) (concat (extract v_5542 0 96) (_(_,_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_rm (extract v_5544 96 128) (handleImmediateWithSignExtend v_2906 8 8)));
      pure ()
    pat_end;
    pattern fun (v_2901 : imm int) (v_2902 : Mem) (v_2903 : reg (bv 128)) => do
      v_11291 <- getRegister v_2903;
      v_11293 <- evaluateAddress v_2902;
      v_11294 <- load v_11293 4;
      setRegister (lhs.of_reg v_2903) (concat (extract v_11291 0 96) (_(_,_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_rm v_11294 (handleImmediateWithSignExtend v_2901 8 8)));
      pure ()
    pat_end
