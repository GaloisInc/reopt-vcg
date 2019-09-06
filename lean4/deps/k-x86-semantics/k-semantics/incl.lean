def incl1 : instruction :=
  definst "incl" $ do
    pattern fun (v_3075 : reg (bv 32)) => do
      v_5261 <- getRegister v_3075;
      v_5262 <- eval (add v_5261 (expression.bv_nat 32 1));
      setRegister (lhs.of_reg v_3075) v_5262;
      setRegister af (eq (extract v_5261 28 32) (expression.bv_nat 4 15));
      setRegister of (bit_and (isBitClear v_5261 0) (eq (extract v_5261 1 32) (expression.bv_nat 31 2147483647)));
      setRegister pf (parityFlag (extract v_5262 24 32));
      setRegister sf (isBitSet v_5262 0);
      setRegister zf (zeroFlag v_5262);
      pure ()
    pat_end;
    pattern fun (v_3072 : Mem) => do
      v_9172 <- evaluateAddress v_3072;
      v_9173 <- load v_9172 4;
      v_9174 <- eval (add v_9173 (expression.bv_nat 32 1));
      store v_9172 v_9174 4;
      setRegister af (eq (extract v_9173 28 32) (expression.bv_nat 4 15));
      setRegister of (bit_and (isBitClear v_9173 0) (eq (extract v_9173 1 32) (expression.bv_nat 31 2147483647)));
      setRegister pf (parityFlag (extract v_9174 24 32));
      setRegister sf (isBitSet v_9174 0);
      setRegister zf (zeroFlag v_9174);
      pure ()
    pat_end
