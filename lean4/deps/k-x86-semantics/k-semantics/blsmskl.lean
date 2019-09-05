def blsmskl1 : instruction :=
  definst "blsmskl" $ do
    pattern fun (v_3036 : reg (bv 32)) (v_3037 : reg (bv 32)) => do
      v_5860 <- getRegister v_3036;
      v_5862 <- eval (bv_xor (sub v_5860 (expression.bv_nat 32 1)) v_5860);
      setRegister (lhs.of_reg v_3037) v_5862;
      setRegister af undef;
      setRegister cf (eq v_5860 (expression.bv_nat 32 0));
      setRegister of bit_zero;
      setRegister pf undef;
      setRegister sf (isBitSet v_5862 0);
      setRegister zf bit_zero;
      pure ()
    pat_end;
    pattern fun (v_3033 : Mem) (v_3032 : reg (bv 32)) => do
      v_9396 <- evaluateAddress v_3033;
      v_9397 <- load v_9396 4;
      v_9399 <- eval (bv_xor (sub v_9397 (expression.bv_nat 32 1)) v_9397);
      setRegister (lhs.of_reg v_3032) v_9399;
      setRegister af undef;
      setRegister cf (eq v_9397 (expression.bv_nat 32 0));
      setRegister of bit_zero;
      setRegister pf undef;
      setRegister sf (isBitSet v_9399 0);
      setRegister zf bit_zero;
      pure ()
    pat_end
