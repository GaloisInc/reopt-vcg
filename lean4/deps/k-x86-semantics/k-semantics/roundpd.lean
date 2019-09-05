def roundpd1 : instruction :=
  definst "roundpd" $ do
    pattern fun (v_2873 : imm int) (v_2875 : reg (bv 128)) (v_2876 : reg (bv 128)) => do
      v_5497 <- getRegister v_2875;
      v_5499 <- eval (handleImmediateWithSignExtend v_2873 8 8);
      setRegister (lhs.of_reg v_2876) (concat (_(_,_)_MINT-WRAPPER-SYNTAX cvt_double_to_int64_rm (extract v_5497 0 64) v_5499) (_(_,_)_MINT-WRAPPER-SYNTAX cvt_double_to_int64_rm (extract v_5497 64 128) v_5499));
      pure ()
    pat_end;
    pattern fun (v_2868 : imm int) (v_2869 : Mem) (v_2870 : reg (bv 128)) => do
      v_11259 <- evaluateAddress v_2869;
      v_11260 <- load v_11259 16;
      v_11262 <- eval (handleImmediateWithSignExtend v_2868 8 8);
      setRegister (lhs.of_reg v_2870) (concat (_(_,_)_MINT-WRAPPER-SYNTAX cvt_double_to_int64_rm (extract v_11260 0 64) v_11262) (_(_,_)_MINT-WRAPPER-SYNTAX cvt_double_to_int64_rm (extract v_11260 64 128) v_11262));
      pure ()
    pat_end
