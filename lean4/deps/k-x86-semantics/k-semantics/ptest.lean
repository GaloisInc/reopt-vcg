def ptest1 : instruction :=
  definst "ptest" $ do
    pattern fun (v_3216 : reg (bv 128)) (v_3217 : reg (bv 128)) => do
      v_8642 <- getRegister v_3217;
      v_8643 <- getRegister v_3216;
      setRegister af bit_zero;
      setRegister cf (eq (bv_and (bv_xor v_8642 (expression.bv_nat 128 340282366920938463463374607431768211455)) v_8643) (expression.bv_nat 128 0));
      setRegister of bit_zero;
      setRegister pf bit_zero;
      setRegister sf bit_zero;
      setRegister zf (zeroFlag (bv_and v_8642 v_8643));
      pure ()
    pat_end;
    pattern fun (v_3213 : Mem) (v_3212 : reg (bv 128)) => do
      v_15099 <- getRegister v_3212;
      v_15100 <- evaluateAddress v_3213;
      v_15101 <- load v_15100 16;
      setRegister af bit_zero;
      setRegister cf (eq (bv_and (bv_xor v_15099 (expression.bv_nat 128 340282366920938463463374607431768211455)) v_15101) (expression.bv_nat 128 0));
      setRegister of bit_zero;
      setRegister pf bit_zero;
      setRegister sf bit_zero;
      setRegister zf (zeroFlag (bv_and v_15099 v_15101));
      pure ()
    pat_end
