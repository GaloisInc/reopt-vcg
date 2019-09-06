def incw1 : instruction :=
  definst "incw" $ do
    pattern fun (v_3089 : reg (bv 16)) => do
      v_5303 <- getRegister v_3089;
      v_5304 <- eval (add v_5303 (expression.bv_nat 16 1));
      setRegister (lhs.of_reg v_3089) v_5304;
      setRegister af (eq (extract v_5303 12 16) (expression.bv_nat 4 15));
      setRegister of (bit_and (isBitClear v_5303 0) (eq (extract v_5303 1 16) (expression.bv_nat 15 32767)));
      setRegister pf (parityFlag (extract v_5304 8 16));
      setRegister sf (isBitSet v_5304 0);
      setRegister zf (zeroFlag v_5304);
      pure ()
    pat_end;
    pattern fun (v_3086 : Mem) => do
      v_9210 <- evaluateAddress v_3086;
      v_9211 <- load v_9210 2;
      v_9212 <- eval (add v_9211 (expression.bv_nat 16 1));
      store v_9210 v_9212 2;
      setRegister af (eq (extract v_9211 12 16) (expression.bv_nat 4 15));
      setRegister of (bit_and (isBitClear v_9211 0) (eq (extract v_9211 1 16) (expression.bv_nat 15 32767)));
      setRegister pf (parityFlag (extract v_9212 8 16));
      setRegister sf (isBitSet v_9212 0);
      setRegister zf (zeroFlag v_9212);
      pure ()
    pat_end
