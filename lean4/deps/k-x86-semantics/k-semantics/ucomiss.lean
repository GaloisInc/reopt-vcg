def ucomiss1 : instruction :=
  definst "ucomiss" $ do
    pattern fun (v_2615 : reg (bv 128)) (v_2616 : reg (bv 128)) => do
      v_4743 <- getRegister v_2616;
      v_4745 <- getRegister v_2615;
      v_4747 <- eval (_(_,_)_MINT-WRAPPER-SYNTAX comiss (extract v_4743 96 128) (extract v_4745 96 128));
      v_4748 <- eval (eq v_4747 (expression.bv_nat 2 0));
      setRegister af bit_zero;
      setRegister cf (bit_or v_4748 (eq v_4747 (expression.bv_nat 2 2)));
      setRegister of bit_zero;
      setRegister pf v_4748;
      setRegister sf bit_zero;
      setRegister zf (bit_or v_4748 (eq v_4747 (expression.bv_nat 2 3)));
      pure ()
    pat_end;
    pattern fun (v_2608 : Mem) (v_2611 : reg (bv 128)) => do
      v_9069 <- getRegister v_2611;
      v_9071 <- evaluateAddress v_2608;
      v_9072 <- load v_9071 4;
      v_9073 <- eval (_(_,_)_MINT-WRAPPER-SYNTAX comiss (extract v_9069 96 128) v_9072);
      v_9074 <- eval (eq v_9073 (expression.bv_nat 2 0));
      setRegister af bit_zero;
      setRegister cf (bit_or v_9074 (eq v_9073 (expression.bv_nat 2 2)));
      setRegister of bit_zero;
      setRegister pf v_9074;
      setRegister sf bit_zero;
      setRegister zf (bit_or v_9074 (eq v_9073 (expression.bv_nat 2 3)));
      pure ()
    pat_end
