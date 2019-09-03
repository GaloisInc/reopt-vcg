def ptest1 : instruction :=
  definst "ptest" $ do
    pattern fun (v_3167 : reg (bv 128)) (v_3168 : reg (bv 128)) => do
      v_8707 <- getRegister v_3168;
      v_8709 <- getRegister v_3167;
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (expression.bv_nat 1 0);
      setRegister af (expression.bv_nat 1 0);
      setRegister zf (zeroFlag (bv_and v_8707 v_8709));
      setRegister sf (expression.bv_nat 1 0);
      setRegister cf (mux (eq (bv_and (bv_xor v_8707 (expression.bv_nat 128 340282366920938463463374607431768211455)) v_8709) (expression.bv_nat 128 0)) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_3163 : Mem) (v_3164 : reg (bv 128)) => do
      v_15301 <- getRegister v_3164;
      v_15303 <- evaluateAddress v_3163;
      v_15304 <- load v_15303 16;
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (expression.bv_nat 1 0);
      setRegister af (expression.bv_nat 1 0);
      setRegister zf (zeroFlag (bv_and v_15301 v_15304));
      setRegister sf (expression.bv_nat 1 0);
      setRegister cf (mux (eq (bv_and (bv_xor v_15301 (expression.bv_nat 128 340282366920938463463374607431768211455)) v_15304) (expression.bv_nat 128 0)) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end
