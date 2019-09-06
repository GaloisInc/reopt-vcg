def vcomiss1 : instruction :=
  definst "vcomiss" $ do
    pattern fun (v_3084 : reg (bv 128)) (v_3085 : reg (bv 128)) => do
      v_5719 <- getRegister v_3085;
      v_5721 <- getRegister v_3084;
      v_5723 <- eval (_(_,_)_MINT-WRAPPER-SYNTAX comiss (extract v_5719 96 128) (extract v_5721 96 128));
      v_5724 <- eval (eq v_5723 (expression.bv_nat 2 0));
      setRegister af bit_zero;
      setRegister cf (bit_or v_5724 (eq v_5723 (expression.bv_nat 2 2)));
      setRegister of bit_zero;
      setRegister pf v_5724;
      setRegister sf bit_zero;
      setRegister zf (bit_or v_5724 (eq v_5723 (expression.bv_nat 2 3)));
      pure ()
    pat_end;
    pattern fun (v_3077 : Mem) (v_3080 : reg (bv 128)) => do
      v_9867 <- getRegister v_3080;
      v_9869 <- evaluateAddress v_3077;
      v_9870 <- load v_9869 4;
      v_9871 <- eval (_(_,_)_MINT-WRAPPER-SYNTAX comiss (extract v_9867 96 128) v_9870);
      v_9872 <- eval (eq v_9871 (expression.bv_nat 2 0));
      setRegister af bit_zero;
      setRegister cf (bit_or v_9872 (eq v_9871 (expression.bv_nat 2 2)));
      setRegister of bit_zero;
      setRegister pf v_9872;
      setRegister sf bit_zero;
      setRegister zf (bit_or v_9872 (eq v_9871 (expression.bv_nat 2 3)));
      pure ()
    pat_end
