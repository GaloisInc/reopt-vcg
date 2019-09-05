def negq1 : instruction :=
  definst "negq" $ do
    pattern fun (v_2899 : reg (bv 64)) => do
      v_4465 <- getRegister v_2899;
      v_4467 <- eval (add (expression.bv_nat 64 1) (bv_xor v_4465 (expression.bv_nat 64 18446744073709551615)));
      v_4469 <- eval (isBitSet v_4467 0);
      setRegister (lhs.of_reg v_2899) v_4467;
      setRegister af (notBool_ (eq (isBitSet v_4465 59) (isBitSet v_4467 59)));
      setRegister cf (notBool_ (eq v_4465 (expression.bv_nat 64 0)));
      setRegister of (bit_and (isBitSet v_4465 0) v_4469);
      setRegister pf (parityFlag (extract v_4467 56 64));
      setRegister sf v_4469;
      setRegister zf (zeroFlag v_4467);
      pure ()
    pat_end;
    pattern fun (v_2896 : Mem) => do
      v_10739 <- evaluateAddress v_2896;
      v_10740 <- load v_10739 8;
      v_10742 <- eval (add (expression.bv_nat 64 1) (bv_xor v_10740 (expression.bv_nat 64 18446744073709551615)));
      store v_10739 v_10742 8;
      v_10745 <- eval (isBitSet v_10742 0);
      setRegister af (notBool_ (eq (isBitSet v_10740 59) (isBitSet v_10742 59)));
      setRegister cf (notBool_ (eq v_10740 (expression.bv_nat 64 0)));
      setRegister of (bit_and (isBitSet v_10740 0) v_10745);
      setRegister pf (parityFlag (extract v_10742 56 64));
      setRegister sf v_10745;
      setRegister zf (zeroFlag v_10742);
      pure ()
    pat_end
