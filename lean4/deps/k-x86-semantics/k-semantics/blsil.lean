def blsil1 : instruction :=
  definst "blsil" $ do
    pattern fun (v_3018 : reg (bv 32)) (v_3019 : reg (bv 32)) => do
      v_5822 <- getRegister v_3018;
      v_5825 <- eval (bv_and (add (expression.bv_nat 32 1) (bv_xor v_5822 (expression.bv_nat 32 4294967295))) v_5822);
      setRegister (lhs.of_reg v_3019) v_5825;
      setRegister af undef;
      setRegister cf (notBool_ (eq v_5822 (expression.bv_nat 32 0)));
      setRegister of bit_zero;
      setRegister pf undef;
      setRegister sf (isBitSet v_5825 0);
      setRegister zf (zeroFlag v_5825);
      pure ()
    pat_end;
    pattern fun (v_3015 : Mem) (v_3014 : reg (bv 32)) => do
      v_9364 <- evaluateAddress v_3015;
      v_9365 <- load v_9364 4;
      v_9368 <- eval (bv_and (add (expression.bv_nat 32 1) (bv_xor v_9365 (expression.bv_nat 32 4294967295))) v_9365);
      setRegister (lhs.of_reg v_3014) v_9368;
      setRegister af undef;
      setRegister cf (notBool_ (eq v_9365 (expression.bv_nat 32 0)));
      setRegister of bit_zero;
      setRegister pf undef;
      setRegister sf (isBitSet v_9368 0);
      setRegister zf (zeroFlag v_9368);
      pure ()
    pat_end
