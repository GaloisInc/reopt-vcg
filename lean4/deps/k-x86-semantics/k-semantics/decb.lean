def decb1 : instruction :=
  definst "decb" $ do
    pattern fun (v_2770 : reg (bv 8)) => do
      v_4406 <- getRegister v_2770;
      v_4407 <- eval (sub v_4406 (expression.bv_nat 8 1));
      setRegister (lhs.of_reg v_2770) v_4407;
      setRegister af (eq (extract v_4406 4 8) (expression.bv_nat 4 0));
      setRegister of (bit_and (isBitSet v_4406 0) (eq (extract v_4406 1 8) (expression.bv_nat 7 0)));
      setRegister pf (parityFlag (extract v_4407 0 8));
      setRegister sf (isBitSet v_4407 0);
      setRegister zf (zeroFlag v_4407);
      pure ()
    pat_end;
    pattern fun (v_2762 : Mem) => do
      v_9067 <- evaluateAddress v_2762;
      v_9068 <- load v_9067 1;
      v_9069 <- eval (sub v_9068 (expression.bv_nat 8 1));
      store v_9067 v_9069 1;
      setRegister af (eq (extract v_9068 4 8) (expression.bv_nat 4 0));
      setRegister of (bit_and (isBitSet v_9068 0) (eq (extract v_9068 1 8) (expression.bv_nat 7 0)));
      setRegister pf (parityFlag (extract v_9069 0 8));
      setRegister sf (isBitSet v_9069 0);
      setRegister zf (zeroFlag v_9069);
      pure ()
    pat_end
