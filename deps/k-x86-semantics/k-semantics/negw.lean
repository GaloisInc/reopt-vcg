def negw : instruction :=
  definst "negw" $ do
    pattern fun (mem_0 : Mem) => do
      v_1 <- evaluateAddress mem_0;
      v_2 <- load v_1 2;
      v_3 <- eval (add (expression.bv_nat 16 1) (bv_xor v_2 (expression.bv_nat 16 65535)));
      store v_1 v_3 2;
      v_5 <- eval (isBitSet v_3 0);
      (v_6 : expression (bv 8)) <- eval (extract v_3 8 16);
      setRegister af (notBool_ (eq (isBitSet v_2 11) (isBitSet v_3 11)));
      setRegister cf (notBool_ (eq v_2 (expression.bv_nat 16 0)));
      setRegister of (bit_and (isBitSet v_2 0) v_5);
      setRegister pf (parityFlag v_6);
      setRegister sf v_5;
      setRegister zf (zeroFlag v_3);
      pure ()
    pat_end;
    pattern fun (r16_0 : reg (bv 16)) => do
      v_1 <- getRegister (lhs.of_reg r16_0);
      v_2 <- eval (add (expression.bv_nat 16 1) (bv_xor v_1 (expression.bv_nat 16 65535)));
      v_3 <- eval (isBitSet v_2 0);
      (v_4 : expression (bv 8)) <- eval (extract v_2 8 16);
      setRegister (lhs.of_reg r16_0) v_2;
      setRegister af (notBool_ (eq (isBitSet v_1 11) (isBitSet v_2 11)));
      setRegister cf (notBool_ (eq v_1 (expression.bv_nat 16 0)));
      setRegister of (bit_and (isBitSet v_1 0) v_3);
      setRegister pf (parityFlag v_4);
      setRegister sf v_3;
      setRegister zf (zeroFlag v_2);
      pure ()
    pat_end
