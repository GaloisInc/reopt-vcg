def comisd1 : instruction :=
  definst "comisd" $ do
    pattern fun (v_2507 : reg (bv 128)) (v_2508 : reg (bv 128)) => do
      v_4037 <- getRegister v_2508;
      v_4039 <- getRegister v_2507;
      v_4041 <- eval (_(_,_)_MINT-WRAPPER-SYNTAX comisd (extract v_4037 64 128) (extract v_4039 64 128));
      v_4042 <- eval (eq v_4041 (expression.bv_nat 2 0));
      setRegister af bit_zero;
      setRegister cf (bit_or v_4042 (eq v_4041 (expression.bv_nat 2 2)));
      setRegister of bit_zero;
      setRegister pf v_4042;
      setRegister sf bit_zero;
      setRegister zf (bit_or v_4042 (eq v_4041 (expression.bv_nat 2 3)));
      pure ()
    pat_end;
    pattern fun (v_2502 : Mem) (v_2503 : reg (bv 128)) => do
      v_7765 <- getRegister v_2503;
      v_7767 <- evaluateAddress v_2502;
      v_7768 <- load v_7767 8;
      v_7769 <- eval (_(_,_)_MINT-WRAPPER-SYNTAX comisd (extract v_7765 64 128) v_7768);
      v_7770 <- eval (eq v_7769 (expression.bv_nat 2 0));
      setRegister af bit_zero;
      setRegister cf (bit_or v_7770 (eq v_7769 (expression.bv_nat 2 2)));
      setRegister of bit_zero;
      setRegister pf v_7770;
      setRegister sf bit_zero;
      setRegister zf (bit_or v_7770 (eq v_7769 (expression.bv_nat 2 3)));
      pure ()
    pat_end
