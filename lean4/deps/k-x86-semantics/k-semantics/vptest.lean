def vptest1 : instruction :=
  definst "vptest" $ do
    pattern fun (v_2571 : reg (bv 128)) (v_2572 : reg (bv 128)) => do
      v_5983 <- getRegister v_2572;
      v_5985 <- getRegister v_2571;
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (expression.bv_nat 1 0);
      setRegister af (expression.bv_nat 1 0);
      setRegister zf (zeroFlag (bv_and v_5983 v_5985));
      setRegister sf (expression.bv_nat 1 0);
      setRegister cf (mux (eq (bv_and (bv_xor v_5983 (expression.bv_nat 128 340282366920938463463374607431768211455)) v_5985) (expression.bv_nat 128 0)) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_2580 : reg (bv 256)) (v_2581 : reg (bv 256)) => do
      v_6001 <- getRegister v_2581;
      v_6003 <- getRegister v_2580;
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (expression.bv_nat 1 0);
      setRegister af (expression.bv_nat 1 0);
      setRegister zf (zeroFlag (bv_and v_6001 v_6003));
      setRegister sf (expression.bv_nat 1 0);
      setRegister cf (mux (eq (bv_and (bv_xor v_6001 (expression.bv_nat 256 115792089237316195423570985008687907853269984665640564039457584007913129639935)) v_6003) (expression.bv_nat 256 0)) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_2567 : Mem) (v_2568 : reg (bv 128)) => do
      v_12453 <- getRegister v_2568;
      v_12455 <- evaluateAddress v_2567;
      v_12456 <- load v_12455 16;
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (expression.bv_nat 1 0);
      setRegister af (expression.bv_nat 1 0);
      setRegister zf (zeroFlag (bv_and v_12453 v_12456));
      setRegister sf (expression.bv_nat 1 0);
      setRegister cf (mux (eq (bv_and (bv_xor v_12453 (expression.bv_nat 128 340282366920938463463374607431768211455)) v_12456) (expression.bv_nat 128 0)) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_2576 : Mem) (v_2577 : reg (bv 256)) => do
      v_12468 <- getRegister v_2577;
      v_12470 <- evaluateAddress v_2576;
      v_12471 <- load v_12470 32;
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (expression.bv_nat 1 0);
      setRegister af (expression.bv_nat 1 0);
      setRegister zf (zeroFlag (bv_and v_12468 v_12471));
      setRegister sf (expression.bv_nat 1 0);
      setRegister cf (mux (eq (bv_and (bv_xor v_12468 (expression.bv_nat 256 115792089237316195423570985008687907853269984665640564039457584007913129639935)) v_12471) (expression.bv_nat 256 0)) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end
