def vcomiss1 : instruction :=
  definst "vcomiss" $ do
    pattern fun (v_3057 : reg (bv 128)) (v_3058 : reg (bv 128)) => do
      v_5692 <- getRegister v_3058;
      v_5694 <- getRegister v_3057;
      v_5696 <- eval (_(_,_)_MINT-WRAPPER-SYNTAX comiss (extract v_5692 96 128) (extract v_5694 96 128));
      v_5697 <- eval (eq v_5696 (expression.bv_nat 2 0));
      setRegister af bit_zero;
      setRegister cf (bit_or v_5697 (eq v_5696 (expression.bv_nat 2 2)));
      setRegister of bit_zero;
      setRegister pf v_5697;
      setRegister sf bit_zero;
      setRegister zf (bit_or v_5697 (eq v_5696 (expression.bv_nat 2 3)));
      pure ()
    pat_end;
    pattern fun (v_3052 : Mem) (v_3053 : reg (bv 128)) => do
      v_9840 <- getRegister v_3053;
      v_9842 <- evaluateAddress v_3052;
      v_9843 <- load v_9842 4;
      v_9844 <- eval (_(_,_)_MINT-WRAPPER-SYNTAX comiss (extract v_9840 96 128) v_9843);
      v_9845 <- eval (eq v_9844 (expression.bv_nat 2 0));
      setRegister af bit_zero;
      setRegister cf (bit_or v_9845 (eq v_9844 (expression.bv_nat 2 2)));
      setRegister of bit_zero;
      setRegister pf v_9845;
      setRegister sf bit_zero;
      setRegister zf (bit_or v_9845 (eq v_9844 (expression.bv_nat 2 3)));
      pure ()
    pat_end
