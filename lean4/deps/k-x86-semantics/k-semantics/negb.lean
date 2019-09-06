def negb1 : instruction :=
  definst "negb" $ do
    pattern fun (v_2911 : reg (bv 8)) => do
      v_4442 <- getRegister v_2911;
      v_4444 <- eval (add (expression.bv_nat 8 1) (bv_xor v_4442 (expression.bv_nat 8 255)));
      v_4446 <- eval (isBitSet v_4444 0);
      setRegister (lhs.of_reg v_2911) v_4444;
      setRegister af (notBool_ (eq (isBitSet v_4442 3) (isBitSet v_4444 3)));
      setRegister cf (notBool_ (eq v_4442 (expression.bv_nat 8 0)));
      setRegister of (bit_and (isBitSet v_4442 0) v_4446);
      setRegister pf (parityFlag (extract v_4444 0 8));
      setRegister sf v_4446;
      setRegister zf (zeroFlag v_4444);
      pure ()
    pat_end;
    pattern fun (v_2904 : Mem) => do
      v_10720 <- evaluateAddress v_2904;
      v_10721 <- load v_10720 1;
      v_10723 <- eval (add (expression.bv_nat 8 1) (bv_xor v_10721 (expression.bv_nat 8 255)));
      store v_10720 v_10723 1;
      v_10726 <- eval (isBitSet v_10723 0);
      setRegister af (notBool_ (eq (isBitSet v_10721 3) (isBitSet v_10723 3)));
      setRegister cf (notBool_ (eq v_10721 (expression.bv_nat 8 0)));
      setRegister of (bit_and (isBitSet v_10721 0) v_10726);
      setRegister pf (parityFlag (extract v_10723 0 8));
      setRegister sf v_10726;
      setRegister zf (zeroFlag v_10723);
      pure ()
    pat_end
