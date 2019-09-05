def vucomisd1 : instruction :=
  definst "vucomisd" $ do
    pattern fun (v_3181 : reg (bv 128)) (v_3182 : reg (bv 128)) => do
      v_7475 <- getRegister v_3182;
      v_7477 <- getRegister v_3181;
      v_7479 <- eval (_(_,_)_MINT-WRAPPER-SYNTAX comisd (extract v_7475 64 128) (extract v_7477 64 128));
      v_7480 <- eval (eq v_7479 (expression.bv_nat 2 0));
      setRegister af bit_zero;
      setRegister cf (bit_or v_7480 (eq v_7479 (expression.bv_nat 2 2)));
      setRegister of bit_zero;
      setRegister pf v_7480;
      setRegister sf bit_zero;
      setRegister zf (bit_or v_7480 (eq v_7479 (expression.bv_nat 2 3)));
      pure ()
    pat_end;
    pattern fun (v_3176 : Mem) (v_3177 : reg (bv 128)) => do
      v_13364 <- getRegister v_3177;
      v_13366 <- evaluateAddress v_3176;
      v_13367 <- load v_13366 8;
      v_13368 <- eval (_(_,_)_MINT-WRAPPER-SYNTAX comisd (extract v_13364 64 128) v_13367);
      v_13369 <- eval (eq v_13368 (expression.bv_nat 2 0));
      setRegister af bit_zero;
      setRegister cf (bit_or v_13369 (eq v_13368 (expression.bv_nat 2 2)));
      setRegister of bit_zero;
      setRegister pf v_13369;
      setRegister sf bit_zero;
      setRegister zf (bit_or v_13369 (eq v_13368 (expression.bv_nat 2 3)));
      pure ()
    pat_end
