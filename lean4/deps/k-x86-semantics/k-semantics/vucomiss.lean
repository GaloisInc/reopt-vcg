def vucomiss1 : instruction :=
  definst "vucomiss" $ do
    pattern fun (v_3190 : reg (bv 128)) (v_3191 : reg (bv 128)) => do
      v_7495 <- getRegister v_3191;
      v_7497 <- getRegister v_3190;
      v_7499 <- eval (_(_,_)_MINT-WRAPPER-SYNTAX comiss (extract v_7495 96 128) (extract v_7497 96 128));
      v_7500 <- eval (eq v_7499 (expression.bv_nat 2 0));
      setRegister af bit_zero;
      setRegister cf (bit_or v_7500 (eq v_7499 (expression.bv_nat 2 2)));
      setRegister of bit_zero;
      setRegister pf v_7500;
      setRegister sf bit_zero;
      setRegister zf (bit_or v_7500 (eq v_7499 (expression.bv_nat 2 3)));
      pure ()
    pat_end;
    pattern fun (v_3185 : Mem) (v_3186 : reg (bv 128)) => do
      v_13380 <- getRegister v_3186;
      v_13382 <- evaluateAddress v_3185;
      v_13383 <- load v_13382 4;
      v_13384 <- eval (_(_,_)_MINT-WRAPPER-SYNTAX comiss (extract v_13380 96 128) v_13383);
      v_13385 <- eval (eq v_13384 (expression.bv_nat 2 0));
      setRegister af bit_zero;
      setRegister cf (bit_or v_13385 (eq v_13384 (expression.bv_nat 2 2)));
      setRegister of bit_zero;
      setRegister pf v_13385;
      setRegister sf bit_zero;
      setRegister zf (bit_or v_13385 (eq v_13384 (expression.bv_nat 2 3)));
      pure ()
    pat_end
