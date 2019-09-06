def negl1 : instruction :=
  definst "negl" $ do
    pattern fun (v_2918 : reg (bv 32)) => do
      v_4467 <- getRegister v_2918;
      v_4469 <- eval (add (expression.bv_nat 32 1) (bv_xor v_4467 (expression.bv_nat 32 4294967295)));
      v_4471 <- eval (isBitSet v_4469 0);
      setRegister (lhs.of_reg v_2918) v_4469;
      setRegister af (notBool_ (eq (isBitSet v_4467 27) (isBitSet v_4469 27)));
      setRegister cf (notBool_ (eq v_4467 (expression.bv_nat 32 0)));
      setRegister of (bit_and (isBitSet v_4467 0) v_4471);
      setRegister pf (parityFlag (extract v_4469 24 32));
      setRegister sf v_4471;
      setRegister zf (zeroFlag v_4469);
      pure ()
    pat_end;
    pattern fun (v_2915 : Mem) => do
      v_10743 <- evaluateAddress v_2915;
      v_10744 <- load v_10743 4;
      v_10746 <- eval (add (expression.bv_nat 32 1) (bv_xor v_10744 (expression.bv_nat 32 4294967295)));
      store v_10743 v_10746 4;
      v_10749 <- eval (isBitSet v_10746 0);
      setRegister af (notBool_ (eq (isBitSet v_10744 27) (isBitSet v_10746 27)));
      setRegister cf (notBool_ (eq v_10744 (expression.bv_nat 32 0)));
      setRegister of (bit_and (isBitSet v_10744 0) v_10749);
      setRegister pf (parityFlag (extract v_10746 24 32));
      setRegister sf v_10749;
      setRegister zf (zeroFlag v_10746);
      pure ()
    pat_end
