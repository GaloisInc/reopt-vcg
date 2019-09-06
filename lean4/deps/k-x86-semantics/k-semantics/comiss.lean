def comiss1 : instruction :=
  definst "comiss" $ do
    pattern fun (v_2542 : reg (bv 128)) (v_2543 : reg (bv 128)) => do
      v_4078 <- getRegister v_2543;
      v_4080 <- getRegister v_2542;
      v_4082 <- eval (_(_,_)_MINT-WRAPPER-SYNTAX comiss (extract v_4078 96 128) (extract v_4080 96 128));
      v_4083 <- eval (eq v_4082 (expression.bv_nat 2 0));
      setRegister af bit_zero;
      setRegister cf (bit_or v_4083 (eq v_4082 (expression.bv_nat 2 2)));
      setRegister of bit_zero;
      setRegister pf v_4083;
      setRegister sf bit_zero;
      setRegister zf (bit_or v_4083 (eq v_4082 (expression.bv_nat 2 3)));
      pure ()
    pat_end;
    pattern fun (v_2538 : Mem) (v_2539 : reg (bv 128)) => do
      v_7791 <- getRegister v_2539;
      v_7793 <- evaluateAddress v_2538;
      v_7794 <- load v_7793 4;
      v_7795 <- eval (_(_,_)_MINT-WRAPPER-SYNTAX comiss (extract v_7791 96 128) v_7794);
      v_7796 <- eval (eq v_7795 (expression.bv_nat 2 0));
      setRegister af bit_zero;
      setRegister cf (bit_or v_7796 (eq v_7795 (expression.bv_nat 2 2)));
      setRegister of bit_zero;
      setRegister pf v_7796;
      setRegister sf bit_zero;
      setRegister zf (bit_or v_7796 (eq v_7795 (expression.bv_nat 2 3)));
      pure ()
    pat_end
