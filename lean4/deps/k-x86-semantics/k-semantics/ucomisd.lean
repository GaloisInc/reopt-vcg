def ucomisd1 : instruction :=
  definst "ucomisd" $ do
    pattern fun (v_2579 : reg (bv 128)) (v_2580 : reg (bv 128)) => do
      v_4696 <- getRegister v_2580;
      v_4698 <- getRegister v_2579;
      v_4700 <- eval (_(_,_)_MINT-WRAPPER-SYNTAX comisd (extract v_4696 64 128) (extract v_4698 64 128));
      v_4701 <- eval (eq v_4700 (expression.bv_nat 2 0));
      setRegister af bit_zero;
      setRegister cf (bit_or v_4701 (eq v_4700 (expression.bv_nat 2 2)));
      setRegister of bit_zero;
      setRegister pf v_4701;
      setRegister sf bit_zero;
      setRegister zf (bit_or v_4701 (eq v_4700 (expression.bv_nat 2 3)));
      pure ()
    pat_end;
    pattern fun (v_2574 : Mem) (v_2575 : reg (bv 128)) => do
      v_9026 <- getRegister v_2575;
      v_9028 <- evaluateAddress v_2574;
      v_9029 <- load v_9028 8;
      v_9030 <- eval (_(_,_)_MINT-WRAPPER-SYNTAX comisd (extract v_9026 64 128) v_9029);
      v_9031 <- eval (eq v_9030 (expression.bv_nat 2 0));
      setRegister af bit_zero;
      setRegister cf (bit_or v_9031 (eq v_9030 (expression.bv_nat 2 2)));
      setRegister of bit_zero;
      setRegister pf v_9031;
      setRegister sf bit_zero;
      setRegister zf (bit_or v_9031 (eq v_9030 (expression.bv_nat 2 3)));
      pure ()
    pat_end
