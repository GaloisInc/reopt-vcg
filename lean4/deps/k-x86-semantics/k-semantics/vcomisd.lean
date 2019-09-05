def vcomisd1 : instruction :=
  definst "vcomisd" $ do
    pattern fun (v_3048 : reg (bv 128)) (v_3049 : reg (bv 128)) => do
      v_5672 <- getRegister v_3049;
      v_5674 <- getRegister v_3048;
      v_5676 <- eval (_(_,_)_MINT-WRAPPER-SYNTAX comisd (extract v_5672 64 128) (extract v_5674 64 128));
      v_5677 <- eval (eq v_5676 (expression.bv_nat 2 0));
      setRegister af bit_zero;
      setRegister cf (bit_or v_5677 (eq v_5676 (expression.bv_nat 2 2)));
      setRegister of bit_zero;
      setRegister pf v_5677;
      setRegister sf bit_zero;
      setRegister zf (bit_or v_5677 (eq v_5676 (expression.bv_nat 2 3)));
      pure ()
    pat_end;
    pattern fun (v_3043 : Mem) (v_3044 : reg (bv 128)) => do
      v_9824 <- getRegister v_3044;
      v_9826 <- evaluateAddress v_3043;
      v_9827 <- load v_9826 8;
      v_9828 <- eval (_(_,_)_MINT-WRAPPER-SYNTAX comisd (extract v_9824 64 128) v_9827);
      v_9829 <- eval (eq v_9828 (expression.bv_nat 2 0));
      setRegister af bit_zero;
      setRegister cf (bit_or v_9829 (eq v_9828 (expression.bv_nat 2 2)));
      setRegister of bit_zero;
      setRegister pf v_9829;
      setRegister sf bit_zero;
      setRegister zf (bit_or v_9829 (eq v_9828 (expression.bv_nat 2 3)));
      pure ()
    pat_end
