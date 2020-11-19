def incw : instruction :=
  definst "incw" $ do
    pattern fun (mem_0 : Mem) => do
      v_1 <- evaluateAddress mem_0;
      v_2 <- load v_1 2;
      v_3 <- eval (add v_2 (expression.bv_nat 16 1));
      store v_1 v_3 2;
      (v_5 : expression (bv 8)) <- eval (extract v_3 8 16);
      (v_6 : expression (bv 15)) <- eval (extract v_2 1 16);
      (v_7 : expression (bv 4)) <- eval (extract v_2 12 16);
      setRegister af (eq v_7 (expression.bv_nat 4 15));
      setRegister of (bit_and (isBitClear v_2 0) (eq v_6 (expression.bv_nat 15 32767)));
      setRegister pf (parityFlag v_5);
      setRegister sf (isBitSet v_3 0);
      setRegister zf (zeroFlag v_3);
      pure ()
    pat_end;
    pattern fun (r16_0 : reg (bv 16)) => do
      v_1 <- getRegister (lhs.of_reg r16_0);
      v_2 <- eval (add v_1 (expression.bv_nat 16 1));
      (v_3 : expression (bv 8)) <- eval (extract v_2 8 16);
      (v_4 : expression (bv 15)) <- eval (extract v_1 1 16);
      (v_5 : expression (bv 4)) <- eval (extract v_1 12 16);
      setRegister (lhs.of_reg r16_0) v_2;
      setRegister af (eq v_5 (expression.bv_nat 4 15));
      setRegister of (bit_and (isBitClear v_1 0) (eq v_4 (expression.bv_nat 15 32767)));
      setRegister pf (parityFlag v_3);
      setRegister sf (isBitSet v_2 0);
      setRegister zf (zeroFlag v_2);
      pure ()
    pat_end
