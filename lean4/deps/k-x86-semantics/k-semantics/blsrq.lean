def blsrq1 : instruction :=
  definst "blsrq" $ do
    pattern fun (v_3064 : reg (bv 64)) (v_3065 : reg (bv 64)) => do
      v_5909 <- getRegister v_3064;
      v_5911 <- eval (bv_and (sub v_5909 (expression.bv_nat 64 1)) v_5909);
      setRegister (lhs.of_reg v_3065) v_5911;
      setRegister af undef;
      setRegister cf (eq v_5909 (expression.bv_nat 64 0));
      setRegister of bit_zero;
      setRegister pf undef;
      setRegister sf (isBitSet v_5911 0);
      setRegister zf (zeroFlag v_5911);
      pure ()
    pat_end;
    pattern fun (v_3059 : Mem) (v_3060 : reg (bv 64)) => do
      v_9436 <- evaluateAddress v_3059;
      v_9437 <- load v_9436 8;
      v_9439 <- eval (bv_and (sub v_9437 (expression.bv_nat 64 1)) v_9437);
      setRegister (lhs.of_reg v_3060) v_9439;
      setRegister af undef;
      setRegister cf (eq v_9437 (expression.bv_nat 64 0));
      setRegister of bit_zero;
      setRegister pf undef;
      setRegister sf (isBitSet v_9439 0);
      setRegister zf (zeroFlag v_9439);
      pure ()
    pat_end
