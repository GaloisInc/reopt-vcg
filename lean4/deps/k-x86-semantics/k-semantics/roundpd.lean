def roundpd1 : instruction :=
  definst "roundpd" $ do
    pattern fun (v_2820 : imm int) (v_2822 : reg (bv 128)) (v_2823 : reg (bv 128)) => do
      v_5773 <- getRegister v_2822;
      v_5775 <- eval (handleImmediateWithSignExtend v_2820 8 8);
      setRegister (lhs.of_reg v_2823) (concat (_(_,_)_MINT-WRAPPER-SYNTAX cvt_double_to_int64_rm (extract v_5773 0 64) v_5775) (_(_,_)_MINT-WRAPPER-SYNTAX cvt_double_to_int64_rm (extract v_5773 64 128) v_5775));
      pure ()
    pat_end;
    pattern fun (v_2816 : imm int) (v_2815 : Mem) (v_2817 : reg (bv 128)) => do
      v_12876 <- evaluateAddress v_2815;
      v_12877 <- load v_12876 16;
      v_12879 <- eval (handleImmediateWithSignExtend v_2816 8 8);
      setRegister (lhs.of_reg v_2817) (concat (_(_,_)_MINT-WRAPPER-SYNTAX cvt_double_to_int64_rm (extract v_12877 0 64) v_12879) (_(_,_)_MINT-WRAPPER-SYNTAX cvt_double_to_int64_rm (extract v_12877 64 128) v_12879));
      pure ()
    pat_end
