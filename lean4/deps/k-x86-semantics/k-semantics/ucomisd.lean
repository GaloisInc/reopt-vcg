def ucomisd1 : instruction :=
  definst "ucomisd" $ do
    pattern fun (v_2528 : reg (bv 128)) (v_2529 : reg (bv 128)) => do
      v_4729 <- getRegister v_2529;
      v_4731 <- getRegister v_2528;
      v_4733 <- eval (_(_,_)_MINT-WRAPPER-SYNTAX comisd (extract v_4729 64 128) (extract v_4731 64 128));
      v_4734 <- eval (eq v_4733 (expression.bv_nat 2 0));
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (mux v_4734 (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister af (expression.bv_nat 1 0);
      setRegister zf (mux (bit_or v_4734 (eq v_4733 (expression.bv_nat 2 3))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister sf (expression.bv_nat 1 0);
      setRegister cf (mux (bit_or v_4734 (eq v_4733 (expression.bv_nat 2 2))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_2521 : Mem) (v_2524 : reg (bv 128)) => do
      v_10302 <- getRegister v_2524;
      v_10304 <- evaluateAddress v_2521;
      v_10305 <- load v_10304 8;
      v_10306 <- eval (_(_,_)_MINT-WRAPPER-SYNTAX comisd (extract v_10302 64 128) v_10305);
      v_10307 <- eval (eq v_10306 (expression.bv_nat 2 0));
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (mux v_10307 (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister af (expression.bv_nat 1 0);
      setRegister zf (mux (bit_or v_10307 (eq v_10306 (expression.bv_nat 2 3))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister sf (expression.bv_nat 1 0);
      setRegister cf (mux (bit_or v_10307 (eq v_10306 (expression.bv_nat 2 2))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end
