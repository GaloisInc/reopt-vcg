def blsiq1 : instruction :=
  definst "blsiq" $ do
    pattern fun (v_2977 : reg (bv 64)) (v_2978 : reg (bv 64)) => do
      v_6065 <- getRegister v_2977;
      v_6070 <- eval (add (expression.bv_nat 64 1) (bv_xor v_6065 (expression.bv_nat 64 18446744073709551615)));
      v_6074 <- eval (bv_and v_6070 v_6065);
      setRegister (lhs.of_reg v_2978) v_6074;
      setRegister of (expression.bv_nat 1 0);
      setRegister pf undef;
      setRegister zf (zeroFlag v_6074);
      setRegister af undef;
      setRegister sf (bv_and (extract v_6070 0 1) (extract v_6065 0 1));
      setRegister cf (mux (notBool_ (eq v_6065 (expression.bv_nat 64 0))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_2972 : Mem) (v_2973 : reg (bv 64)) => do
      v_9898 <- evaluateAddress v_2972;
      v_9899 <- load v_9898 8;
      v_9904 <- eval (add (expression.bv_nat 64 1) (bv_xor v_9899 (expression.bv_nat 64 18446744073709551615)));
      v_9908 <- eval (bv_and v_9904 v_9899);
      setRegister (lhs.of_reg v_2973) v_9908;
      setRegister of (expression.bv_nat 1 0);
      setRegister pf undef;
      setRegister zf (zeroFlag v_9908);
      setRegister af undef;
      setRegister sf (bv_and (extract v_9904 0 1) (extract v_9899 0 1));
      setRegister cf (mux (notBool_ (eq v_9899 (expression.bv_nat 64 0))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end
