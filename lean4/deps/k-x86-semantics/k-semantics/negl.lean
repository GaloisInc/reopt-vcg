def negl1 : instruction :=
  definst "negl" $ do
    pattern fun (v_2893 : reg (bv 32)) => do
      v_4440 <- getRegister v_2893;
      v_4442 <- eval (add (expression.bv_nat 32 1) (bv_xor v_4440 (expression.bv_nat 32 4294967295)));
      v_4444 <- eval (isBitSet v_4442 0);
      setRegister (lhs.of_reg v_2893) v_4442;
      setRegister af (notBool_ (eq (isBitSet v_4440 27) (isBitSet v_4442 27)));
      setRegister cf (notBool_ (eq v_4440 (expression.bv_nat 32 0)));
      setRegister of (bit_and (isBitSet v_4440 0) v_4444);
      setRegister pf (parityFlag (extract v_4442 24 32));
      setRegister sf v_4444;
      setRegister zf (zeroFlag v_4442);
      pure ()
    pat_end;
    pattern fun (v_2889 : Mem) => do
      v_10716 <- evaluateAddress v_2889;
      v_10717 <- load v_10716 4;
      v_10719 <- eval (add (expression.bv_nat 32 1) (bv_xor v_10717 (expression.bv_nat 32 4294967295)));
      store v_10716 v_10719 4;
      v_10722 <- eval (isBitSet v_10719 0);
      setRegister af (notBool_ (eq (isBitSet v_10717 27) (isBitSet v_10719 27)));
      setRegister cf (notBool_ (eq v_10717 (expression.bv_nat 32 0)));
      setRegister of (bit_and (isBitSet v_10717 0) v_10722);
      setRegister pf (parityFlag (extract v_10719 24 32));
      setRegister sf v_10722;
      setRegister zf (zeroFlag v_10719);
      pure ()
    pat_end
