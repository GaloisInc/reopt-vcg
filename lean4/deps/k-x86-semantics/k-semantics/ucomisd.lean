def ucomisd1 : instruction :=
  definst "ucomisd" $ do
    pattern fun (v_2606 : reg (bv 128)) (v_2607 : reg (bv 128)) => do
      v_4723 <- getRegister v_2607;
      v_4725 <- getRegister v_2606;
      v_4727 <- eval (_(_,_)_MINT-WRAPPER-SYNTAX comisd (extract v_4723 64 128) (extract v_4725 64 128));
      v_4728 <- eval (eq v_4727 (expression.bv_nat 2 0));
      setRegister af bit_zero;
      setRegister cf (bit_or v_4728 (eq v_4727 (expression.bv_nat 2 2)));
      setRegister of bit_zero;
      setRegister pf v_4728;
      setRegister sf bit_zero;
      setRegister zf (bit_or v_4728 (eq v_4727 (expression.bv_nat 2 3)));
      pure ()
    pat_end;
    pattern fun (v_2599 : Mem) (v_2602 : reg (bv 128)) => do
      v_9053 <- getRegister v_2602;
      v_9055 <- evaluateAddress v_2599;
      v_9056 <- load v_9055 8;
      v_9057 <- eval (_(_,_)_MINT-WRAPPER-SYNTAX comisd (extract v_9053 64 128) v_9056);
      v_9058 <- eval (eq v_9057 (expression.bv_nat 2 0));
      setRegister af bit_zero;
      setRegister cf (bit_or v_9058 (eq v_9057 (expression.bv_nat 2 2)));
      setRegister of bit_zero;
      setRegister pf v_9058;
      setRegister sf bit_zero;
      setRegister zf (bit_or v_9058 (eq v_9057 (expression.bv_nat 2 3)));
      pure ()
    pat_end
