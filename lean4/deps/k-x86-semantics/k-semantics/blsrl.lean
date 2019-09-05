def blsrl1 : instruction :=
  definst "blsrl" $ do
    pattern fun (v_3054 : reg (bv 32)) (v_3055 : reg (bv 32)) => do
      v_5892 <- getRegister v_3054;
      v_5894 <- eval (bv_and (sub v_5892 (expression.bv_nat 32 1)) v_5892);
      setRegister (lhs.of_reg v_3055) v_5894;
      setRegister af undef;
      setRegister cf (eq v_5892 (expression.bv_nat 32 0));
      setRegister of bit_zero;
      setRegister pf undef;
      setRegister sf (isBitSet v_5894 0);
      setRegister zf (zeroFlag v_5894);
      pure ()
    pat_end;
    pattern fun (v_3051 : Mem) (v_3050 : reg (bv 32)) => do
      v_9422 <- evaluateAddress v_3051;
      v_9423 <- load v_9422 4;
      v_9425 <- eval (bv_and (sub v_9423 (expression.bv_nat 32 1)) v_9423);
      setRegister (lhs.of_reg v_3050) v_9425;
      setRegister af undef;
      setRegister cf (eq v_9423 (expression.bv_nat 32 0));
      setRegister of bit_zero;
      setRegister pf undef;
      setRegister sf (isBitSet v_9425 0);
      setRegister zf (zeroFlag v_9425);
      pure ()
    pat_end
