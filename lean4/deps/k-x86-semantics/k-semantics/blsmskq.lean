def blsmskq1 : instruction :=
  definst "blsmskq" $ do
    pattern fun (v_3072 : reg (bv 64)) (v_3073 : reg (bv 64)) => do
      v_5757 <- getRegister v_3072;
      v_5759 <- eval (bv_xor (sub v_5757 (expression.bv_nat 64 1)) v_5757);
      setRegister (lhs.of_reg v_3073) v_5759;
      setRegister af undef;
      setRegister cf (eq v_5757 (expression.bv_nat 64 0));
      setRegister of bit_zero;
      setRegister pf undef;
      setRegister sf (isBitSet v_5759 0);
      setRegister zf bit_zero;
      pure ()
    pat_end;
    pattern fun (v_3068 : Mem) (v_3069 : reg (bv 64)) => do
      v_9233 <- evaluateAddress v_3068;
      v_9234 <- load v_9233 8;
      v_9236 <- eval (bv_xor (sub v_9234 (expression.bv_nat 64 1)) v_9234);
      setRegister (lhs.of_reg v_3069) v_9236;
      setRegister af undef;
      setRegister cf (eq v_9234 (expression.bv_nat 64 0));
      setRegister of bit_zero;
      setRegister pf undef;
      setRegister sf (isBitSet v_9236 0);
      setRegister zf bit_zero;
      pure ()
    pat_end
