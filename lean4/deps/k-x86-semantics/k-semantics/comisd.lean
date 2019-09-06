def comisd1 : instruction :=
  definst "comisd" $ do
    pattern fun (v_2533 : reg (bv 128)) (v_2534 : reg (bv 128)) => do
      v_4058 <- getRegister v_2534;
      v_4060 <- getRegister v_2533;
      v_4062 <- eval (_(_,_)_MINT-WRAPPER-SYNTAX comisd (extract v_4058 64 128) (extract v_4060 64 128));
      v_4063 <- eval (eq v_4062 (expression.bv_nat 2 0));
      setRegister af bit_zero;
      setRegister cf (bit_or v_4063 (eq v_4062 (expression.bv_nat 2 2)));
      setRegister of bit_zero;
      setRegister pf v_4063;
      setRegister sf bit_zero;
      setRegister zf (bit_or v_4063 (eq v_4062 (expression.bv_nat 2 3)));
      pure ()
    pat_end;
    pattern fun (v_2529 : Mem) (v_2530 : reg (bv 128)) => do
      v_7775 <- getRegister v_2530;
      v_7777 <- evaluateAddress v_2529;
      v_7778 <- load v_7777 8;
      v_7779 <- eval (_(_,_)_MINT-WRAPPER-SYNTAX comisd (extract v_7775 64 128) v_7778);
      v_7780 <- eval (eq v_7779 (expression.bv_nat 2 0));
      setRegister af bit_zero;
      setRegister cf (bit_or v_7780 (eq v_7779 (expression.bv_nat 2 2)));
      setRegister of bit_zero;
      setRegister pf v_7780;
      setRegister sf bit_zero;
      setRegister zf (bit_or v_7780 (eq v_7779 (expression.bv_nat 2 3)));
      pure ()
    pat_end
