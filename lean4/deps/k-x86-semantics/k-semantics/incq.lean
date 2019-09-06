def incq1 : instruction :=
  definst "incq" $ do
    pattern fun (v_3082 : reg (bv 64)) => do
      v_5282 <- getRegister v_3082;
      v_5283 <- eval (add v_5282 (expression.bv_nat 64 1));
      setRegister (lhs.of_reg v_3082) v_5283;
      setRegister af (eq (extract v_5282 60 64) (expression.bv_nat 4 15));
      setRegister of (bit_and (isBitClear v_5282 0) (eq (extract v_5282 1 64) (expression.bv_nat 63 9223372036854775807)));
      setRegister pf (parityFlag (extract v_5283 56 64));
      setRegister sf (isBitSet v_5283 0);
      setRegister zf (zeroFlag v_5283);
      pure ()
    pat_end;
    pattern fun (v_3079 : Mem) => do
      v_9191 <- evaluateAddress v_3079;
      v_9192 <- load v_9191 8;
      v_9193 <- eval (add v_9192 (expression.bv_nat 64 1));
      store v_9191 v_9193 8;
      setRegister af (eq (extract v_9192 60 64) (expression.bv_nat 4 15));
      setRegister of (bit_and (isBitClear v_9192 0) (eq (extract v_9192 1 64) (expression.bv_nat 63 9223372036854775807)));
      setRegister pf (parityFlag (extract v_9193 56 64));
      setRegister sf (isBitSet v_9193 0);
      setRegister zf (zeroFlag v_9193);
      pure ()
    pat_end
