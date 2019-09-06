def roundsd1 : instruction :=
  definst "roundsd" $ do
    pattern fun (v_2920 : imm int) (v_2923 : reg (bv 128)) (v_2924 : reg (bv 128)) => do
      v_5237 <- getRegister v_2924;
      v_5239 <- getRegister v_2923;
      setRegister (lhs.of_reg v_2924) (concat (extract v_5237 0 64) (_(_,_)_MINT-WRAPPER-SYNTAX cvt_double_to_int64_rm (extract v_5239 64 128) (handleImmediateWithSignExtend v_2920 8 8)));
      pure ()
    pat_end;
    pattern fun (v_2915 : imm int) (v_2916 : Mem) (v_2919 : reg (bv 128)) => do
      v_10539 <- getRegister v_2919;
      v_10541 <- evaluateAddress v_2916;
      v_10542 <- load v_10541 8;
      setRegister (lhs.of_reg v_2919) (concat (extract v_10539 0 64) (_(_,_)_MINT-WRAPPER-SYNTAX cvt_double_to_int64_rm v_10542 (handleImmediateWithSignExtend v_2915 8 8)));
      pure ()
    pat_end
