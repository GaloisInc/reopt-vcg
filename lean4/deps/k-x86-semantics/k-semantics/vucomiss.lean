def vucomiss1 : instruction :=
  definst "vucomiss" $ do
    pattern fun (v_3217 : reg (bv 128)) (v_3218 : reg (bv 128)) => do
      v_7522 <- getRegister v_3218;
      v_7524 <- getRegister v_3217;
      v_7526 <- eval (_(_,_)_MINT-WRAPPER-SYNTAX comiss (extract v_7522 96 128) (extract v_7524 96 128));
      v_7527 <- eval (eq v_7526 (expression.bv_nat 2 0));
      setRegister af bit_zero;
      setRegister cf (bit_or v_7527 (eq v_7526 (expression.bv_nat 2 2)));
      setRegister of bit_zero;
      setRegister pf v_7527;
      setRegister sf bit_zero;
      setRegister zf (bit_or v_7527 (eq v_7526 (expression.bv_nat 2 3)));
      pure ()
    pat_end;
    pattern fun (v_3212 : Mem) (v_3213 : reg (bv 128)) => do
      v_13407 <- getRegister v_3213;
      v_13409 <- evaluateAddress v_3212;
      v_13410 <- load v_13409 4;
      v_13411 <- eval (_(_,_)_MINT-WRAPPER-SYNTAX comiss (extract v_13407 96 128) v_13410);
      v_13412 <- eval (eq v_13411 (expression.bv_nat 2 0));
      setRegister af bit_zero;
      setRegister cf (bit_or v_13412 (eq v_13411 (expression.bv_nat 2 2)));
      setRegister of bit_zero;
      setRegister pf v_13412;
      setRegister sf bit_zero;
      setRegister zf (bit_or v_13412 (eq v_13411 (expression.bv_nat 2 3)));
      pure ()
    pat_end
