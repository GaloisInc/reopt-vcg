def incl1 : instruction :=
  definst "incl" $ do
    pattern fun (v_3049 : reg (bv 32)) => do
      v_5242 <- getRegister v_3049;
      v_5243 <- eval (add v_5242 (expression.bv_nat 32 1));
      setRegister (lhs.of_reg v_3049) v_5243;
      setRegister af (eq (extract v_5242 28 32) (expression.bv_nat 4 15));
      setRegister of (bit_and (notBool_ (isBitSet v_5242 0)) (eq (extract v_5242 1 32) (expression.bv_nat 31 2147483647)));
      setRegister pf (parityFlag (extract v_5243 24 32));
      setRegister sf (isBitSet v_5243 0);
      setRegister zf (zeroFlag v_5243);
      pure ()
    pat_end;
    pattern fun (v_3045 : Mem) => do
      v_9163 <- evaluateAddress v_3045;
      v_9164 <- load v_9163 4;
      v_9165 <- eval (add v_9164 (expression.bv_nat 32 1));
      store v_9163 v_9165 4;
      setRegister af (eq (extract v_9164 28 32) (expression.bv_nat 4 15));
      setRegister of (bit_and (notBool_ (isBitSet v_9164 0)) (eq (extract v_9164 1 32) (expression.bv_nat 31 2147483647)));
      setRegister pf (parityFlag (extract v_9165 24 32));
      setRegister sf (isBitSet v_9165 0);
      setRegister zf (zeroFlag v_9165);
      pure ()
    pat_end
