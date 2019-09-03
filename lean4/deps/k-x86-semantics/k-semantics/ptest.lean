def ptest1 : instruction :=
  definst "ptest" $ do
    pattern fun (v_3153 : reg (bv 128)) (v_3154 : reg (bv 128)) => do
      v_9025 <- getRegister v_3154;
      v_9029 <- getRegister v_3153;
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (expression.bv_nat 1 0);
      setRegister af (expression.bv_nat 1 0);
      setRegister zf (zeroFlag (bv_and v_9025 v_9029));
      setRegister sf (expression.bv_nat 1 0);
      setRegister cf (mux (eq (bv_and (bv_xor v_9025 (mi (bitwidthMInt v_9025) -1)) v_9029) (expression.bv_nat 128 0)) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_3148 : Mem) (v_3149 : reg (bv 128)) => do
      v_15918 <- getRegister v_3149;
      v_15922 <- evaluateAddress v_3148;
      v_15923 <- load v_15922 16;
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (expression.bv_nat 1 0);
      setRegister af (expression.bv_nat 1 0);
      setRegister zf (zeroFlag (bv_and v_15918 v_15923));
      setRegister sf (expression.bv_nat 1 0);
      setRegister cf (mux (eq (bv_and (bv_xor v_15918 (mi (bitwidthMInt v_15918) -1)) v_15923) (expression.bv_nat 128 0)) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end
