def decl1 : instruction :=
  definst "decl" $ do
    pattern fun (v_2750 : reg (bv 32)) => do
      v_4406 <- getRegister v_2750;
      v_4407 <- eval (sub v_4406 (expression.bv_nat 32 1));
      setRegister (lhs.of_reg v_2750) v_4407;
      setRegister af (eq (extract v_4406 28 32) (expression.bv_nat 4 0));
      setRegister of (bit_and (isBitSet v_4406 0) (eq (extract v_4406 1 32) (expression.bv_nat 31 0)));
      setRegister pf (parityFlag (extract v_4407 24 32));
      setRegister sf (isBitSet v_4407 0);
      setRegister zf (zeroFlag v_4407);
      pure ()
    pat_end;
    pattern fun (v_2746 : Mem) => do
      v_9076 <- evaluateAddress v_2746;
      v_9077 <- load v_9076 4;
      v_9078 <- eval (sub v_9077 (expression.bv_nat 32 1));
      store v_9076 v_9078 4;
      setRegister af (eq (extract v_9077 28 32) (expression.bv_nat 4 0));
      setRegister of (bit_and (isBitSet v_9077 0) (eq (extract v_9077 1 32) (expression.bv_nat 31 0)));
      setRegister pf (parityFlag (extract v_9078 24 32));
      setRegister sf (isBitSet v_9078 0);
      setRegister zf (zeroFlag v_9078);
      pure ()
    pat_end
