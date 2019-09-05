def comiss1 : instruction :=
  definst "comiss" $ do
    pattern fun (v_2516 : reg (bv 128)) (v_2517 : reg (bv 128)) => do
      v_4057 <- getRegister v_2517;
      v_4059 <- getRegister v_2516;
      v_4061 <- eval (_(_,_)_MINT-WRAPPER-SYNTAX comiss (extract v_4057 96 128) (extract v_4059 96 128));
      v_4062 <- eval (eq v_4061 (expression.bv_nat 2 0));
      setRegister af bit_zero;
      setRegister cf (bit_or v_4062 (eq v_4061 (expression.bv_nat 2 2)));
      setRegister of bit_zero;
      setRegister pf v_4062;
      setRegister sf bit_zero;
      setRegister zf (bit_or v_4062 (eq v_4061 (expression.bv_nat 2 3)));
      pure ()
    pat_end;
    pattern fun (v_2511 : Mem) (v_2512 : reg (bv 128)) => do
      v_7781 <- getRegister v_2512;
      v_7783 <- evaluateAddress v_2511;
      v_7784 <- load v_7783 4;
      v_7785 <- eval (_(_,_)_MINT-WRAPPER-SYNTAX comiss (extract v_7781 96 128) v_7784);
      v_7786 <- eval (eq v_7785 (expression.bv_nat 2 0));
      setRegister af bit_zero;
      setRegister cf (bit_or v_7786 (eq v_7785 (expression.bv_nat 2 2)));
      setRegister of bit_zero;
      setRegister pf v_7786;
      setRegister sf bit_zero;
      setRegister zf (bit_or v_7786 (eq v_7785 (expression.bv_nat 2 3)));
      pure ()
    pat_end
