def vcomisd1 : instruction :=
  definst "vcomisd" $ do
    pattern fun (v_3075 : reg (bv 128)) (v_3076 : reg (bv 128)) => do
      v_5699 <- getRegister v_3076;
      v_5701 <- getRegister v_3075;
      v_5703 <- eval (_(_,_)_MINT-WRAPPER-SYNTAX comisd (extract v_5699 64 128) (extract v_5701 64 128));
      v_5704 <- eval (eq v_5703 (expression.bv_nat 2 0));
      setRegister af bit_zero;
      setRegister cf (bit_or v_5704 (eq v_5703 (expression.bv_nat 2 2)));
      setRegister of bit_zero;
      setRegister pf v_5704;
      setRegister sf bit_zero;
      setRegister zf (bit_or v_5704 (eq v_5703 (expression.bv_nat 2 3)));
      pure ()
    pat_end;
    pattern fun (v_3068 : Mem) (v_3071 : reg (bv 128)) => do
      v_9851 <- getRegister v_3071;
      v_9853 <- evaluateAddress v_3068;
      v_9854 <- load v_9853 8;
      v_9855 <- eval (_(_,_)_MINT-WRAPPER-SYNTAX comisd (extract v_9851 64 128) v_9854);
      v_9856 <- eval (eq v_9855 (expression.bv_nat 2 0));
      setRegister af bit_zero;
      setRegister cf (bit_or v_9856 (eq v_9855 (expression.bv_nat 2 2)));
      setRegister of bit_zero;
      setRegister pf v_9856;
      setRegister sf bit_zero;
      setRegister zf (bit_or v_9856 (eq v_9855 (expression.bv_nat 2 3)));
      pure ()
    pat_end
