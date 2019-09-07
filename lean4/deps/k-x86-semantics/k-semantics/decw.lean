def decw1 : instruction :=
  definst "decw" $ do
    pattern fun (mem_0 : Mem) => do
      v_1 <- evaluateAddress mem_0;
      v_2 <- load v_1 2;
      v_3 <- eval (sub v_2 (expression.bv_nat 16 1));
      store v_1 v_3 2;
      setRegister af (eq (extract v_2 12 16) (expression.bv_nat 4 0));
      setRegister of (bit_and (isBitSet v_2 0) (eq (extract v_2 1 16) (expression.bv_nat 15 0)));
      setRegister pf (parityFlag (extract v_3 8 16));
      setRegister sf (isBitSet v_3 0);
      setRegister zf (zeroFlag v_3);
      pure ()
    pat_end;
    pattern fun (r16_0 : reg (bv 16)) => do
      v_1 <- getRegister r16_0;
      v_2 <- eval (sub v_1 (expression.bv_nat 16 1));
      setRegister (lhs.of_reg r16_0) v_2;
      setRegister af (eq (extract v_1 12 16) (expression.bv_nat 4 0));
      setRegister of (bit_and (isBitSet v_1 0) (eq (extract v_1 1 16) (expression.bv_nat 15 0)));
      setRegister pf (parityFlag (extract v_2 8 16));
      setRegister sf (isBitSet v_2 0);
      setRegister zf (zeroFlag v_2);
      pure ()
    pat_end
