def blsiq1 : instruction :=
  definst "blsiq" $ do
    pattern fun (v_3054 : reg (bv 64)) (v_3055 : reg (bv 64)) => do
      v_5722 <- getRegister v_3054;
      v_5725 <- eval (bv_and (add (expression.bv_nat 64 1) (bv_xor v_5722 (expression.bv_nat 64 18446744073709551615))) v_5722);
      setRegister (lhs.of_reg v_3055) v_5725;
      setRegister af undef;
      setRegister cf (notBool_ (eq v_5722 (expression.bv_nat 64 0)));
      setRegister of bit_zero;
      setRegister pf undef;
      setRegister sf (isBitSet v_5725 0);
      setRegister zf (zeroFlag v_5725);
      pure ()
    pat_end;
    pattern fun (v_3050 : Mem) (v_3051 : reg (bv 64)) => do
      v_9204 <- evaluateAddress v_3050;
      v_9205 <- load v_9204 8;
      v_9208 <- eval (bv_and (add (expression.bv_nat 64 1) (bv_xor v_9205 (expression.bv_nat 64 18446744073709551615))) v_9205);
      setRegister (lhs.of_reg v_3051) v_9208;
      setRegister af undef;
      setRegister cf (notBool_ (eq v_9205 (expression.bv_nat 64 0)));
      setRegister of bit_zero;
      setRegister pf undef;
      setRegister sf (isBitSet v_9208 0);
      setRegister zf (zeroFlag v_9208);
      pure ()
    pat_end
