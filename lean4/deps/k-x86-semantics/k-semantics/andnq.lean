def andnq1 : instruction :=
  definst "andnq" $ do
    pattern fun (v_2903 : reg (bv 64)) (v_2904 : reg (bv 64)) (v_2905 : reg (bv 64)) => do
      v_5276 <- getRegister v_2904;
      v_5278 <- getRegister v_2903;
      v_5279 <- eval (bv_and (bv_xor v_5276 (expression.bv_nat 64 18446744073709551615)) v_5278);
      setRegister (lhs.of_reg v_2905) v_5279;
      setRegister af undef;
      setRegister cf bit_zero;
      setRegister of bit_zero;
      setRegister pf undef;
      setRegister sf (bit_and (notBool_ (eq (isBitSet v_5276 0) (bv1ToBool (expression.bv_nat 1 1)))) (isBitSet v_5278 0));
      setRegister zf (zeroFlag v_5279);
      pure ()
    pat_end;
    pattern fun (v_2898 : Mem) (v_2899 : reg (bv 64)) (v_2900 : reg (bv 64)) => do
      v_9002 <- getRegister v_2899;
      v_9004 <- evaluateAddress v_2898;
      v_9005 <- load v_9004 8;
      v_9006 <- eval (bv_and (bv_xor v_9002 (expression.bv_nat 64 18446744073709551615)) v_9005);
      setRegister (lhs.of_reg v_2900) v_9006;
      setRegister af undef;
      setRegister cf bit_zero;
      setRegister of bit_zero;
      setRegister pf undef;
      setRegister sf (bit_and (notBool_ (eq (isBitSet v_9002 0) (bv1ToBool (expression.bv_nat 1 1)))) (isBitSet v_9005 0));
      setRegister zf (zeroFlag v_9006);
      pure ()
    pat_end
