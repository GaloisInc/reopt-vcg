def blsiq1 : instruction :=
  definst "blsiq" $ do
    pattern fun (v_3028 : reg (bv 64)) (v_3029 : reg (bv 64)) => do
      v_5841 <- getRegister v_3028;
      v_5844 <- eval (bv_and (add (expression.bv_nat 64 1) (bv_xor v_5841 (expression.bv_nat 64 18446744073709551615))) v_5841);
      setRegister (lhs.of_reg v_3029) v_5844;
      setRegister af undef;
      setRegister cf (notBool_ (eq v_5841 (expression.bv_nat 64 0)));
      setRegister of bit_zero;
      setRegister pf undef;
      setRegister sf (isBitSet v_5844 0);
      setRegister zf (zeroFlag v_5844);
      pure ()
    pat_end;
    pattern fun (v_3023 : Mem) (v_3024 : reg (bv 64)) => do
      v_9380 <- evaluateAddress v_3023;
      v_9381 <- load v_9380 8;
      v_9384 <- eval (bv_and (add (expression.bv_nat 64 1) (bv_xor v_9381 (expression.bv_nat 64 18446744073709551615))) v_9381);
      setRegister (lhs.of_reg v_3024) v_9384;
      setRegister af undef;
      setRegister cf (notBool_ (eq v_9381 (expression.bv_nat 64 0)));
      setRegister of bit_zero;
      setRegister pf undef;
      setRegister sf (isBitSet v_9384 0);
      setRegister zf (zeroFlag v_9384);
      pure ()
    pat_end
