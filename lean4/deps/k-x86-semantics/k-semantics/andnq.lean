def andnq1 : instruction :=
  definst "andnq" $ do
    pattern fun (v_2877 : reg (bv 64)) (v_2878 : reg (bv 64)) (v_2879 : reg (bv 64)) => do
      v_5395 <- getRegister v_2878;
      v_5397 <- getRegister v_2877;
      v_5398 <- eval (bv_and (bv_xor v_5395 (expression.bv_nat 64 18446744073709551615)) v_5397);
      setRegister (lhs.of_reg v_2879) v_5398;
      setRegister af undef;
      setRegister cf bit_zero;
      setRegister of bit_zero;
      setRegister pf undef;
      setRegister sf (bit_and (notBool_ (eq (isBitSet v_5395 0) (bv1ToBool (expression.bv_nat 1 1)))) (isBitSet v_5397 0));
      setRegister zf (zeroFlag v_5398);
      pure ()
    pat_end;
    pattern fun (v_2871 : Mem) (v_2872 : reg (bv 64)) (v_2873 : reg (bv 64)) => do
      v_9178 <- getRegister v_2872;
      v_9180 <- evaluateAddress v_2871;
      v_9181 <- load v_9180 8;
      v_9182 <- eval (bv_and (bv_xor v_9178 (expression.bv_nat 64 18446744073709551615)) v_9181);
      setRegister (lhs.of_reg v_2873) v_9182;
      setRegister af undef;
      setRegister cf bit_zero;
      setRegister of bit_zero;
      setRegister pf undef;
      setRegister sf (bit_and (notBool_ (eq (isBitSet v_9178 0) (bv1ToBool (expression.bv_nat 1 1)))) (isBitSet v_9181 0));
      setRegister zf (zeroFlag v_9182);
      pure ()
    pat_end
