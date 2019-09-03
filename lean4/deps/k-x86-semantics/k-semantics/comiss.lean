def comiss1 : instruction :=
  definst "comiss" $ do
    pattern fun (v_2464 : reg (bv 128)) (v_2465 : reg (bv 128)) => do
      v_4030 <- getRegister v_2465;
      v_4032 <- getRegister v_2464;
      v_4034 <- eval (_(_,_)_MINT-WRAPPER-SYNTAX comiss (extract v_4030 96 128) (extract v_4032 96 128));
      v_4035 <- eval (eq v_4034 (expression.bv_nat 2 0));
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (mux v_4035 (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister af (expression.bv_nat 1 0);
      setRegister zf (mux (bit_or v_4035 (eq v_4034 (expression.bv_nat 2 3))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister sf (expression.bv_nat 1 0);
      setRegister cf (mux (bit_or v_4035 (eq v_4034 (expression.bv_nat 2 2))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_2458 : Mem) (v_2460 : reg (bv 128)) => do
      v_8272 <- getRegister v_2460;
      v_8274 <- evaluateAddress v_2458;
      v_8275 <- load v_8274 4;
      v_8276 <- eval (_(_,_)_MINT-WRAPPER-SYNTAX comiss (extract v_8272 96 128) v_8275);
      v_8277 <- eval (eq v_8276 (expression.bv_nat 2 0));
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (mux v_8277 (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister af (expression.bv_nat 1 0);
      setRegister zf (mux (bit_or v_8277 (eq v_8276 (expression.bv_nat 2 3))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister sf (expression.bv_nat 1 0);
      setRegister cf (mux (bit_or v_8277 (eq v_8276 (expression.bv_nat 2 2))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end
