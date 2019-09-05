def ucomiss1 : instruction :=
  definst "ucomiss" $ do
    pattern fun (v_2588 : reg (bv 128)) (v_2589 : reg (bv 128)) => do
      v_4716 <- getRegister v_2589;
      v_4718 <- getRegister v_2588;
      v_4720 <- eval (_(_,_)_MINT-WRAPPER-SYNTAX comiss (extract v_4716 96 128) (extract v_4718 96 128));
      v_4721 <- eval (eq v_4720 (expression.bv_nat 2 0));
      setRegister af bit_zero;
      setRegister cf (bit_or v_4721 (eq v_4720 (expression.bv_nat 2 2)));
      setRegister of bit_zero;
      setRegister pf v_4721;
      setRegister sf bit_zero;
      setRegister zf (bit_or v_4721 (eq v_4720 (expression.bv_nat 2 3)));
      pure ()
    pat_end;
    pattern fun (v_2583 : Mem) (v_2584 : reg (bv 128)) => do
      v_9042 <- getRegister v_2584;
      v_9044 <- evaluateAddress v_2583;
      v_9045 <- load v_9044 4;
      v_9046 <- eval (_(_,_)_MINT-WRAPPER-SYNTAX comiss (extract v_9042 96 128) v_9045);
      v_9047 <- eval (eq v_9046 (expression.bv_nat 2 0));
      setRegister af bit_zero;
      setRegister cf (bit_or v_9047 (eq v_9046 (expression.bv_nat 2 2)));
      setRegister of bit_zero;
      setRegister pf v_9047;
      setRegister sf bit_zero;
      setRegister zf (bit_or v_9047 (eq v_9046 (expression.bv_nat 2 3)));
      pure ()
    pat_end
