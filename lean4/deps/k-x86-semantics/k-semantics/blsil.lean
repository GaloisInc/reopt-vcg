def blsil1 : instruction :=
  definst "blsil" $ do
    pattern fun (v_3046 : reg (bv 32)) (v_3047 : reg (bv 32)) => do
      v_5703 <- getRegister v_3046;
      v_5706 <- eval (bv_and (add (expression.bv_nat 32 1) (bv_xor v_5703 (expression.bv_nat 32 4294967295))) v_5703);
      setRegister (lhs.of_reg v_3047) v_5706;
      setRegister af undef;
      setRegister cf (notBool_ (eq v_5703 (expression.bv_nat 32 0)));
      setRegister of bit_zero;
      setRegister pf undef;
      setRegister sf (isBitSet v_5706 0);
      setRegister zf (zeroFlag v_5706);
      pure ()
    pat_end;
    pattern fun (v_3041 : Mem) (v_3042 : reg (bv 32)) => do
      v_9188 <- evaluateAddress v_3041;
      v_9189 <- load v_9188 4;
      v_9192 <- eval (bv_and (add (expression.bv_nat 32 1) (bv_xor v_9189 (expression.bv_nat 32 4294967295))) v_9189);
      setRegister (lhs.of_reg v_3042) v_9192;
      setRegister af undef;
      setRegister cf (notBool_ (eq v_9189 (expression.bv_nat 32 0)));
      setRegister of bit_zero;
      setRegister pf undef;
      setRegister sf (isBitSet v_9192 0);
      setRegister zf (zeroFlag v_9192);
      pure ()
    pat_end
