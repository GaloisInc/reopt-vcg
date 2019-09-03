def ucomisd1 : instruction :=
  definst "ucomisd" $ do
    pattern fun (v_2515 : reg (bv 128)) (v_2516 : reg (bv 128)) => do
      v_4718 <- getRegister v_2516;
      v_4720 <- getRegister v_2515;
      v_4722 <- eval (_(_,_)_MINT-WRAPPER-SYNTAX comisd (extract v_4718 64 128) (extract v_4720 64 128));
      v_4723 <- eval (eq v_4722 (expression.bv_nat 2 0));
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (mux v_4723 (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister af (expression.bv_nat 1 0);
      setRegister zf (mux (bit_or v_4723 (eq v_4722 (expression.bv_nat 2 3))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister sf (expression.bv_nat 1 0);
      setRegister cf (mux (bit_or v_4723 (eq v_4722 (expression.bv_nat 2 2))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_2508 : Mem) (v_2511 : reg (bv 128)) => do
      v_9208 <- getRegister v_2511;
      v_9210 <- evaluateAddress v_2508;
      v_9211 <- load v_9210 8;
      v_9212 <- eval (_(_,_)_MINT-WRAPPER-SYNTAX comisd (extract v_9208 64 128) v_9211);
      v_9213 <- eval (eq v_9212 (expression.bv_nat 2 0));
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (mux v_9213 (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister af (expression.bv_nat 1 0);
      setRegister zf (mux (bit_or v_9213 (eq v_9212 (expression.bv_nat 2 3))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister sf (expression.bv_nat 1 0);
      setRegister cf (mux (bit_or v_9213 (eq v_9212 (expression.bv_nat 2 2))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end
