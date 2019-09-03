def roundss1 : instruction :=
  definst "roundss" $ do
    pattern fun (v_2840 : imm int) (v_2843 : reg (bv 128)) (v_2844 : reg (bv 128)) => do
      v_5800 <- getRegister v_2844;
      v_5802 <- getRegister v_2843;
      setRegister (lhs.of_reg v_2844) (concat (extract v_5800 0 96) (_(_,_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_rm (extract v_5802 96 128) (handleImmediateWithSignExtend v_2840 8 8)));
      pure ()
    pat_end;
    pattern fun (v_2835 : imm int) (v_2836 : Mem) (v_2839 : reg (bv 128)) => do
      v_12984 <- getRegister v_2839;
      v_12986 <- evaluateAddress v_2836;
      v_12987 <- load v_12986 4;
      setRegister (lhs.of_reg v_2839) (concat (extract v_12984 0 96) (_(_,_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_rm v_12987 (handleImmediateWithSignExtend v_2835 8 8)));
      pure ()
    pat_end
