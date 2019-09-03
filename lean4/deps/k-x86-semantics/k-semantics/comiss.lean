def comiss1 : instruction :=
  definst "comiss" $ do
    pattern fun (v_2451 : reg (bv 128)) (v_2452 : reg (bv 128)) => do
      v_4043 <- getRegister v_2452;
      v_4045 <- getRegister v_2451;
      v_4047 <- eval (_(_,_)_MINT-WRAPPER-SYNTAX comiss (extract v_4043 96 128) (extract v_4045 96 128));
      v_4048 <- eval (eq v_4047 (expression.bv_nat 2 0));
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (mux v_4048 (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister af (expression.bv_nat 1 0);
      setRegister zf (mux (bit_or v_4048 (eq v_4047 (expression.bv_nat 2 3))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister sf (expression.bv_nat 1 0);
      setRegister cf (mux (bit_or v_4048 (eq v_4047 (expression.bv_nat 2 2))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_2447 : Mem) (v_2448 : reg (bv 128)) => do
      v_8000 <- getRegister v_2448;
      v_8002 <- evaluateAddress v_2447;
      v_8003 <- load v_8002 4;
      v_8004 <- eval (_(_,_)_MINT-WRAPPER-SYNTAX comiss (extract v_8000 96 128) v_8003);
      v_8005 <- eval (eq v_8004 (expression.bv_nat 2 0));
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (mux v_8005 (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister af (expression.bv_nat 1 0);
      setRegister zf (mux (bit_or v_8005 (eq v_8004 (expression.bv_nat 2 3))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister sf (expression.bv_nat 1 0);
      setRegister cf (mux (bit_or v_8005 (eq v_8004 (expression.bv_nat 2 2))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end
