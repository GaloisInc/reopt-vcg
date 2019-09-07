def negl1 : instruction :=
  definst "negl" $ do
    pattern fun (mem_0 : Mem) => do
      v_1 <- evaluateAddress mem_0;
      v_2 <- load v_1 4;
      v_3 <- eval (add (expression.bv_nat 32 1) (bv_xor v_2 (expression.bv_nat 32 4294967295)));
      store v_1 v_3 4;
      v_5 <- eval (isBitSet v_3 0);
      setRegister af (notBool_ (eq (isBitSet v_2 27) (isBitSet v_3 27)));
      setRegister cf (notBool_ (eq v_2 (expression.bv_nat 32 0)));
      setRegister of (bit_and (isBitSet v_2 0) v_5);
      setRegister pf (parityFlag (extract v_3 24 32));
      setRegister sf v_5;
      setRegister zf (zeroFlag v_3);
      pure ()
    pat_end;
    pattern fun (r32_0 : reg (bv 32)) => do
      v_1 <- getRegister r32_0;
      v_2 <- eval (add (expression.bv_nat 32 1) (bv_xor v_1 (expression.bv_nat 32 4294967295)));
      v_3 <- eval (isBitSet v_2 0);
      setRegister (lhs.of_reg r32_0) v_2;
      setRegister af (notBool_ (eq (isBitSet v_1 27) (isBitSet v_2 27)));
      setRegister cf (notBool_ (eq v_1 (expression.bv_nat 32 0)));
      setRegister of (bit_and (isBitSet v_1 0) v_3);
      setRegister pf (parityFlag (extract v_2 24 32));
      setRegister sf v_3;
      setRegister zf (zeroFlag v_2);
      pure ()
    pat_end
