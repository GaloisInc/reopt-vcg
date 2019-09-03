def comisd1 : instruction :=
  definst "comisd" $ do
    pattern fun (v_2455 : reg (bv 128)) (v_2456 : reg (bv 128)) => do
      v_4007 <- getRegister v_2456;
      v_4009 <- getRegister v_2455;
      v_4011 <- eval (_(_,_)_MINT-WRAPPER-SYNTAX comisd (extract v_4007 64 128) (extract v_4009 64 128));
      v_4012 <- eval (eq v_4011 (expression.bv_nat 2 0));
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (mux v_4012 (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister af (expression.bv_nat 1 0);
      setRegister zf (mux (bit_or v_4012 (eq v_4011 (expression.bv_nat 2 3))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister sf (expression.bv_nat 1 0);
      setRegister cf (mux (bit_or v_4012 (eq v_4011 (expression.bv_nat 2 2))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_2449 : Mem) (v_2451 : reg (bv 128)) => do
      v_8253 <- getRegister v_2451;
      v_8255 <- evaluateAddress v_2449;
      v_8256 <- load v_8255 8;
      v_8257 <- eval (_(_,_)_MINT-WRAPPER-SYNTAX comisd (extract v_8253 64 128) v_8256);
      v_8258 <- eval (eq v_8257 (expression.bv_nat 2 0));
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (mux v_8258 (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister af (expression.bv_nat 1 0);
      setRegister zf (mux (bit_or v_8258 (eq v_8257 (expression.bv_nat 2 3))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister sf (expression.bv_nat 1 0);
      setRegister cf (mux (bit_or v_8258 (eq v_8257 (expression.bv_nat 2 2))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end
