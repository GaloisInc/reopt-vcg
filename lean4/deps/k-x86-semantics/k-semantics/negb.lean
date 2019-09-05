def negb1 : instruction :=
  definst "negb" $ do
    pattern fun (v_2885 : reg (bv 8)) => do
      v_4415 <- getRegister v_2885;
      v_4417 <- eval (add (expression.bv_nat 8 1) (bv_xor v_4415 (expression.bv_nat 8 255)));
      v_4419 <- eval (isBitSet v_4417 0);
      setRegister (lhs.of_reg v_2885) v_4417;
      setRegister af (notBool_ (eq (isBitSet v_4415 3) (isBitSet v_4417 3)));
      setRegister cf (notBool_ (eq v_4415 (expression.bv_nat 8 0)));
      setRegister of (bit_and (isBitSet v_4415 0) v_4419);
      setRegister pf (parityFlag (extract v_4417 0 8));
      setRegister sf v_4419;
      setRegister zf (zeroFlag v_4417);
      pure ()
    pat_end;
    pattern fun (v_2878 : Mem) => do
      v_10693 <- evaluateAddress v_2878;
      v_10694 <- load v_10693 1;
      v_10696 <- eval (add (expression.bv_nat 8 1) (bv_xor v_10694 (expression.bv_nat 8 255)));
      store v_10693 v_10696 1;
      v_10699 <- eval (isBitSet v_10696 0);
      setRegister af (notBool_ (eq (isBitSet v_10694 3) (isBitSet v_10696 3)));
      setRegister cf (notBool_ (eq v_10694 (expression.bv_nat 8 0)));
      setRegister of (bit_and (isBitSet v_10694 0) v_10699);
      setRegister pf (parityFlag (extract v_10696 0 8));
      setRegister sf v_10699;
      setRegister zf (zeroFlag v_10696);
      pure ()
    pat_end
