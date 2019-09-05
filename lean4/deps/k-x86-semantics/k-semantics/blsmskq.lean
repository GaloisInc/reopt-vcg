def blsmskq1 : instruction :=
  definst "blsmskq" $ do
    pattern fun (v_3046 : reg (bv 64)) (v_3047 : reg (bv 64)) => do
      v_5876 <- getRegister v_3046;
      v_5878 <- eval (bv_xor (sub v_5876 (expression.bv_nat 64 1)) v_5876);
      setRegister (lhs.of_reg v_3047) v_5878;
      setRegister af undef;
      setRegister cf (eq v_5876 (expression.bv_nat 64 0));
      setRegister of bit_zero;
      setRegister pf undef;
      setRegister sf (isBitSet v_5878 0);
      setRegister zf bit_zero;
      pure ()
    pat_end;
    pattern fun (v_3041 : Mem) (v_3042 : reg (bv 64)) => do
      v_9409 <- evaluateAddress v_3041;
      v_9410 <- load v_9409 8;
      v_9412 <- eval (bv_xor (sub v_9410 (expression.bv_nat 64 1)) v_9410);
      setRegister (lhs.of_reg v_3042) v_9412;
      setRegister af undef;
      setRegister cf (eq v_9410 (expression.bv_nat 64 0));
      setRegister of bit_zero;
      setRegister pf undef;
      setRegister sf (isBitSet v_9412 0);
      setRegister zf bit_zero;
      pure ()
    pat_end
