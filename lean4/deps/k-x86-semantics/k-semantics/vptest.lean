def vptest1 : instruction :=
  definst "vptest" $ do
    pattern fun (v_2625 : reg (bv 128)) (v_2626 : reg (bv 128)) => do
      v_6034 <- getRegister v_2626;
      v_6035 <- getRegister v_2625;
      setRegister af bit_zero;
      setRegister cf (eq (bv_and (bv_xor v_6034 (expression.bv_nat 128 340282366920938463463374607431768211455)) v_6035) (expression.bv_nat 128 0));
      setRegister of bit_zero;
      setRegister pf bit_zero;
      setRegister sf bit_zero;
      setRegister zf (zeroFlag (bv_and v_6034 v_6035));
      pure ()
    pat_end;
    pattern fun (v_2634 : reg (bv 256)) (v_2635 : reg (bv 256)) => do
      v_6051 <- getRegister v_2635;
      v_6052 <- getRegister v_2634;
      setRegister af bit_zero;
      setRegister cf (eq (bv_and (bv_xor v_6051 (expression.bv_nat 256 115792089237316195423570985008687907853269984665640564039457584007913129639935)) v_6052) (expression.bv_nat 256 0));
      setRegister of bit_zero;
      setRegister pf bit_zero;
      setRegister sf bit_zero;
      setRegister zf (zeroFlag (bv_and v_6051 v_6052));
      pure ()
    pat_end;
    pattern fun (v_2620 : Mem) (v_2621 : reg (bv 128)) => do
      v_12131 <- getRegister v_2621;
      v_12132 <- evaluateAddress v_2620;
      v_12133 <- load v_12132 16;
      setRegister af bit_zero;
      setRegister cf (eq (bv_and (bv_xor v_12131 (expression.bv_nat 128 340282366920938463463374607431768211455)) v_12133) (expression.bv_nat 128 0));
      setRegister of bit_zero;
      setRegister pf bit_zero;
      setRegister sf bit_zero;
      setRegister zf (zeroFlag (bv_and v_12131 v_12133));
      pure ()
    pat_end;
    pattern fun (v_2629 : Mem) (v_2630 : reg (bv 256)) => do
      v_12145 <- getRegister v_2630;
      v_12146 <- evaluateAddress v_2629;
      v_12147 <- load v_12146 32;
      setRegister af bit_zero;
      setRegister cf (eq (bv_and (bv_xor v_12145 (expression.bv_nat 256 115792089237316195423570985008687907853269984665640564039457584007913129639935)) v_12147) (expression.bv_nat 256 0));
      setRegister of bit_zero;
      setRegister pf bit_zero;
      setRegister sf bit_zero;
      setRegister zf (zeroFlag (bv_and v_12145 v_12147));
      pure ()
    pat_end
