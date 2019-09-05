def roundsd1 : instruction :=
  definst "roundsd" $ do
    pattern fun (v_2895 : imm int) (v_2897 : reg (bv 128)) (v_2898 : reg (bv 128)) => do
      v_5529 <- getRegister v_2898;
      v_5531 <- getRegister v_2897;
      setRegister (lhs.of_reg v_2898) (concat (extract v_5529 0 64) (_(_,_)_MINT-WRAPPER-SYNTAX cvt_double_to_int64_rm (extract v_5531 64 128) (handleImmediateWithSignExtend v_2895 8 8)));
      pure ()
    pat_end;
    pattern fun (v_2890 : imm int) (v_2891 : Mem) (v_2892 : reg (bv 128)) => do
      v_11283 <- getRegister v_2892;
      v_11285 <- evaluateAddress v_2891;
      v_11286 <- load v_11285 8;
      setRegister (lhs.of_reg v_2892) (concat (extract v_11283 0 64) (_(_,_)_MINT-WRAPPER-SYNTAX cvt_double_to_int64_rm v_11286 (handleImmediateWithSignExtend v_2890 8 8)));
      pure ()
    pat_end
