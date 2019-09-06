def blsrl1 : instruction :=
  definst "blsrl" $ do
    pattern fun (v_3082 : reg (bv 32)) (v_3083 : reg (bv 32)) => do
      v_5773 <- getRegister v_3082;
      v_5775 <- eval (bv_and (sub v_5773 (expression.bv_nat 32 1)) v_5773);
      setRegister (lhs.of_reg v_3083) v_5775;
      setRegister af undef;
      setRegister cf (eq v_5773 (expression.bv_nat 32 0));
      setRegister of bit_zero;
      setRegister pf undef;
      setRegister sf (isBitSet v_5775 0);
      setRegister zf (zeroFlag v_5775);
      pure ()
    pat_end;
    pattern fun (v_3077 : Mem) (v_3078 : reg (bv 32)) => do
      v_9246 <- evaluateAddress v_3077;
      v_9247 <- load v_9246 4;
      v_9249 <- eval (bv_and (sub v_9247 (expression.bv_nat 32 1)) v_9247);
      setRegister (lhs.of_reg v_3078) v_9249;
      setRegister af undef;
      setRegister cf (eq v_9247 (expression.bv_nat 32 0));
      setRegister of bit_zero;
      setRegister pf undef;
      setRegister sf (isBitSet v_9249 0);
      setRegister zf (zeroFlag v_9249);
      pure ()
    pat_end
