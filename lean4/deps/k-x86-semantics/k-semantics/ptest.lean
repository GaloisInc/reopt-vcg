def ptest1 : instruction :=
  definst "ptest" $ do
    pattern fun (v_3244 : reg (bv 128)) (v_3245 : reg (bv 128)) => do
      v_8669 <- getRegister v_3245;
      v_8670 <- getRegister v_3244;
      setRegister af bit_zero;
      setRegister cf (eq (bv_and (bv_xor v_8669 (expression.bv_nat 128 340282366920938463463374607431768211455)) v_8670) (expression.bv_nat 128 0));
      setRegister of bit_zero;
      setRegister pf bit_zero;
      setRegister sf bit_zero;
      setRegister zf (zeroFlag (bv_and v_8669 v_8670));
      pure ()
    pat_end;
    pattern fun (v_3240 : Mem) (v_3241 : reg (bv 128)) => do
      v_15075 <- getRegister v_3241;
      v_15076 <- evaluateAddress v_3240;
      v_15077 <- load v_15076 16;
      setRegister af bit_zero;
      setRegister cf (eq (bv_and (bv_xor v_15075 (expression.bv_nat 128 340282366920938463463374607431768211455)) v_15077) (expression.bv_nat 128 0));
      setRegister of bit_zero;
      setRegister pf bit_zero;
      setRegister sf bit_zero;
      setRegister zf (zeroFlag (bv_and v_15075 v_15077));
      pure ()
    pat_end
