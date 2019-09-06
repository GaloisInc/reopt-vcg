def incb1 : instruction :=
  definst "incb" $ do
    pattern fun (v_3069 : reg (bv 8)) => do
      v_5240 <- getRegister v_3069;
      v_5241 <- eval (add v_5240 (expression.bv_nat 8 1));
      setRegister (lhs.of_reg v_3069) v_5241;
      setRegister af (eq (extract v_5240 4 8) (expression.bv_nat 4 15));
      setRegister of (bit_and (isBitClear v_5240 0) (eq (extract v_5240 1 8) (expression.bv_nat 7 127)));
      setRegister pf (parityFlag (extract v_5241 0 8));
      setRegister sf (isBitSet v_5241 0);
      setRegister zf (zeroFlag v_5241);
      pure ()
    pat_end;
    pattern fun (v_3061 : Mem) => do
      v_9153 <- evaluateAddress v_3061;
      v_9154 <- load v_9153 1;
      v_9155 <- eval (add v_9154 (expression.bv_nat 8 1));
      store v_9153 v_9155 1;
      setRegister af (eq (extract v_9154 4 8) (expression.bv_nat 4 15));
      setRegister of (bit_and (isBitClear v_9154 0) (eq (extract v_9154 1 8) (expression.bv_nat 7 127)));
      setRegister pf (parityFlag (extract v_9155 0 8));
      setRegister sf (isBitSet v_9155 0);
      setRegister zf (zeroFlag v_9155);
      pure ()
    pat_end
