def incw1 : instruction :=
  definst "incw" $ do
    pattern fun (v_3063 : reg (bv 16)) => do
      v_5286 <- getRegister v_3063;
      v_5287 <- eval (add v_5286 (expression.bv_nat 16 1));
      setRegister (lhs.of_reg v_3063) v_5287;
      setRegister af (eq (extract v_5286 12 16) (expression.bv_nat 4 15));
      setRegister of (bit_and (notBool_ (isBitSet v_5286 0)) (eq (extract v_5286 1 16) (expression.bv_nat 15 32767)));
      setRegister pf (parityFlag (extract v_5287 8 16));
      setRegister sf (isBitSet v_5287 0);
      setRegister zf (zeroFlag v_5287);
      pure ()
    pat_end;
    pattern fun (v_3059 : Mem) => do
      v_9203 <- evaluateAddress v_3059;
      v_9204 <- load v_9203 2;
      v_9205 <- eval (add v_9204 (expression.bv_nat 16 1));
      store v_9203 v_9205 2;
      setRegister af (eq (extract v_9204 12 16) (expression.bv_nat 4 15));
      setRegister of (bit_and (notBool_ (isBitSet v_9204 0)) (eq (extract v_9204 1 16) (expression.bv_nat 15 32767)));
      setRegister pf (parityFlag (extract v_9205 8 16));
      setRegister sf (isBitSet v_9205 0);
      setRegister zf (zeroFlag v_9205);
      pure ()
    pat_end
