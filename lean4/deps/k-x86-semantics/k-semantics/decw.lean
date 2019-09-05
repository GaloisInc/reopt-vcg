def decw1 : instruction :=
  definst "decw" $ do
    pattern fun (v_2764 : reg (bv 16)) => do
      v_4448 <- getRegister v_2764;
      v_4449 <- eval (sub v_4448 (expression.bv_nat 16 1));
      setRegister (lhs.of_reg v_2764) v_4449;
      setRegister af (eq (extract v_4448 12 16) (expression.bv_nat 4 0));
      setRegister of (bit_and (isBitSet v_4448 0) (eq (extract v_4448 1 16) (expression.bv_nat 15 0)));
      setRegister pf (parityFlag (extract v_4449 8 16));
      setRegister sf (isBitSet v_4449 0);
      setRegister zf (zeroFlag v_4449);
      pure ()
    pat_end;
    pattern fun (v_2760 : Mem) => do
      v_9114 <- evaluateAddress v_2760;
      v_9115 <- load v_9114 2;
      v_9116 <- eval (sub v_9115 (expression.bv_nat 16 1));
      store v_9114 v_9116 2;
      setRegister af (eq (extract v_9115 12 16) (expression.bv_nat 4 0));
      setRegister of (bit_and (isBitSet v_9115 0) (eq (extract v_9115 1 16) (expression.bv_nat 15 0)));
      setRegister pf (parityFlag (extract v_9116 8 16));
      setRegister sf (isBitSet v_9116 0);
      setRegister zf (zeroFlag v_9116);
      pure ()
    pat_end
