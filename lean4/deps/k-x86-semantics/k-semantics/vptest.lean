def vptest1 : instruction :=
  definst "vptest" $ do
    pattern fun (v_2652 : reg (bv 128)) (v_2653 : reg (bv 128)) => do
      v_6061 <- getRegister v_2653;
      v_6062 <- getRegister v_2652;
      setRegister af bit_zero;
      setRegister cf (eq (bv_and (bv_xor v_6061 (expression.bv_nat 128 340282366920938463463374607431768211455)) v_6062) (expression.bv_nat 128 0));
      setRegister of bit_zero;
      setRegister pf bit_zero;
      setRegister sf bit_zero;
      setRegister zf (zeroFlag (bv_and v_6061 v_6062));
      pure ()
    pat_end;
    pattern fun (v_2661 : reg (bv 256)) (v_2662 : reg (bv 256)) => do
      v_6078 <- getRegister v_2662;
      v_6079 <- getRegister v_2661;
      setRegister af bit_zero;
      setRegister cf (eq (bv_and (bv_xor v_6078 (expression.bv_nat 256 115792089237316195423570985008687907853269984665640564039457584007913129639935)) v_6079) (expression.bv_nat 256 0));
      setRegister of bit_zero;
      setRegister pf bit_zero;
      setRegister sf bit_zero;
      setRegister zf (zeroFlag (bv_and v_6078 v_6079));
      pure ()
    pat_end;
    pattern fun (v_2647 : Mem) (v_2648 : reg (bv 128)) => do
      v_12158 <- getRegister v_2648;
      v_12159 <- evaluateAddress v_2647;
      v_12160 <- load v_12159 16;
      setRegister af bit_zero;
      setRegister cf (eq (bv_and (bv_xor v_12158 (expression.bv_nat 128 340282366920938463463374607431768211455)) v_12160) (expression.bv_nat 128 0));
      setRegister of bit_zero;
      setRegister pf bit_zero;
      setRegister sf bit_zero;
      setRegister zf (zeroFlag (bv_and v_12158 v_12160));
      pure ()
    pat_end;
    pattern fun (v_2656 : Mem) (v_2657 : reg (bv 256)) => do
      v_12172 <- getRegister v_2657;
      v_12173 <- evaluateAddress v_2656;
      v_12174 <- load v_12173 32;
      setRegister af bit_zero;
      setRegister cf (eq (bv_and (bv_xor v_12172 (expression.bv_nat 256 115792089237316195423570985008687907853269984665640564039457584007913129639935)) v_12174) (expression.bv_nat 256 0));
      setRegister of bit_zero;
      setRegister pf bit_zero;
      setRegister sf bit_zero;
      setRegister zf (zeroFlag (bv_and v_12172 v_12174));
      pure ()
    pat_end
