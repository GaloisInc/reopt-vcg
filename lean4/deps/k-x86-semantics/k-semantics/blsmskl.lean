def blsmskl1 : instruction :=
  definst "blsmskl" $ do
    pattern fun (v_3064 : reg (bv 32)) (v_3065 : reg (bv 32)) => do
      v_5741 <- getRegister v_3064;
      v_5743 <- eval (bv_xor (sub v_5741 (expression.bv_nat 32 1)) v_5741);
      setRegister (lhs.of_reg v_3065) v_5743;
      setRegister af undef;
      setRegister cf (eq v_5741 (expression.bv_nat 32 0));
      setRegister of bit_zero;
      setRegister pf undef;
      setRegister sf (isBitSet v_5743 0);
      setRegister zf bit_zero;
      pure ()
    pat_end;
    pattern fun (v_3059 : Mem) (v_3060 : reg (bv 32)) => do
      v_9220 <- evaluateAddress v_3059;
      v_9221 <- load v_9220 4;
      v_9223 <- eval (bv_xor (sub v_9221 (expression.bv_nat 32 1)) v_9221);
      setRegister (lhs.of_reg v_3060) v_9223;
      setRegister af undef;
      setRegister cf (eq v_9221 (expression.bv_nat 32 0));
      setRegister of bit_zero;
      setRegister pf undef;
      setRegister sf (isBitSet v_9223 0);
      setRegister zf bit_zero;
      pure ()
    pat_end
