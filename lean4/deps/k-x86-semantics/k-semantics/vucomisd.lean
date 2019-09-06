def vucomisd1 : instruction :=
  definst "vucomisd" $ do
    pattern fun (v_3208 : reg (bv 128)) (v_3209 : reg (bv 128)) => do
      v_7502 <- getRegister v_3209;
      v_7504 <- getRegister v_3208;
      v_7506 <- eval (_(_,_)_MINT-WRAPPER-SYNTAX comisd (extract v_7502 64 128) (extract v_7504 64 128));
      v_7507 <- eval (eq v_7506 (expression.bv_nat 2 0));
      setRegister af bit_zero;
      setRegister cf (bit_or v_7507 (eq v_7506 (expression.bv_nat 2 2)));
      setRegister of bit_zero;
      setRegister pf v_7507;
      setRegister sf bit_zero;
      setRegister zf (bit_or v_7507 (eq v_7506 (expression.bv_nat 2 3)));
      pure ()
    pat_end;
    pattern fun (v_3203 : Mem) (v_3204 : reg (bv 128)) => do
      v_13391 <- getRegister v_3204;
      v_13393 <- evaluateAddress v_3203;
      v_13394 <- load v_13393 8;
      v_13395 <- eval (_(_,_)_MINT-WRAPPER-SYNTAX comisd (extract v_13391 64 128) v_13394);
      v_13396 <- eval (eq v_13395 (expression.bv_nat 2 0));
      setRegister af bit_zero;
      setRegister cf (bit_or v_13396 (eq v_13395 (expression.bv_nat 2 2)));
      setRegister of bit_zero;
      setRegister pf v_13396;
      setRegister sf bit_zero;
      setRegister zf (bit_or v_13396 (eq v_13395 (expression.bv_nat 2 3)));
      pure ()
    pat_end
