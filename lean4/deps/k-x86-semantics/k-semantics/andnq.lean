def andnq : instruction :=
  definst "andnq" $ do
    pattern fun (mem_0 : Mem) (r64_1 : reg (bv 64)) (r64_2 : reg (bv 64)) => do
      v_3 <- getRegister (lhs.of_reg r64_1);
      v_4 <- evaluateAddress mem_0;
      v_5 <- load v_4 8;
      v_6 <- eval (bv_and (bv_xor v_3 (expression.bv_nat 64 18446744073709551615)) v_5);
      setRegister (lhs.of_reg r64_2) v_6;
      setRegister af undef;
      setRegister cf bit_zero;
      setRegister of bit_zero;
      setRegister pf undef;
      setRegister sf (bit_and (notBool_ (eq (isBitSet v_3 0) (bv1ToBool (expression.bv_nat 1 1)))) (isBitSet v_5 0));
      setRegister zf (zeroFlag v_6);
      pure ()
    pat_end;
    pattern fun (r64_0 : reg (bv 64)) (r64_1 : reg (bv 64)) (r64_2 : reg (bv 64)) => do
      v_3 <- getRegister (lhs.of_reg r64_1);
      v_4 <- getRegister (lhs.of_reg r64_0);
      v_5 <- eval (bv_and (bv_xor v_3 (expression.bv_nat 64 18446744073709551615)) v_4);
      setRegister (lhs.of_reg r64_2) v_5;
      setRegister af undef;
      setRegister cf bit_zero;
      setRegister of bit_zero;
      setRegister pf undef;
      setRegister sf (bit_and (notBool_ (eq (isBitSet v_3 0) (bv1ToBool (expression.bv_nat 1 1)))) (isBitSet v_4 0));
      setRegister zf (zeroFlag v_5);
      pure ()
    pat_end
