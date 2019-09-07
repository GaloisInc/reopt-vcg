def decl1 : instruction :=
  definst "decl" $ do
    pattern fun (mem_0 : Mem) => do
      v_1 <- evaluateAddress mem_0;
      v_2 <- load v_1 4;
      v_3 <- eval (sub v_2 (expression.bv_nat 32 1));
      store v_1 v_3 4;
      setRegister af (eq (extract v_2 28 32) (expression.bv_nat 4 0));
      setRegister of (bit_and (isBitSet v_2 0) (eq (extract v_2 1 32) (expression.bv_nat 31 0)));
      setRegister pf (parityFlag (extract v_3 24 32));
      setRegister sf (isBitSet v_3 0);
      setRegister zf (zeroFlag v_3);
      pure ()
    pat_end;
    pattern fun (r32_0 : reg (bv 32)) => do
      v_1 <- getRegister r32_0;
      v_2 <- eval (sub v_1 (expression.bv_nat 32 1));
      setRegister (lhs.of_reg r32_0) v_2;
      setRegister af (eq (extract v_1 28 32) (expression.bv_nat 4 0));
      setRegister of (bit_and (isBitSet v_1 0) (eq (extract v_1 1 32) (expression.bv_nat 31 0)));
      setRegister pf (parityFlag (extract v_2 24 32));
      setRegister sf (isBitSet v_2 0);
      setRegister zf (zeroFlag v_2);
      pure ()
    pat_end
