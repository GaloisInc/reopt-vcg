def blsiq1 : instruction :=
  definst "blsiq" $ do
    pattern fun (v_2964 : reg (bv 64)) (v_2965 : reg (bv 64)) => do
      v_5908 <- getRegister v_2964;
      v_5915 <- eval (add (expression.bv_nat 64 1) (bv_xor v_5908 (mi (bitwidthMInt v_5908) -1)));
      v_5919 <- eval (bv_and v_5915 v_5908);
      setRegister (lhs.of_reg v_2965) v_5919;
      setRegister of (expression.bv_nat 1 0);
      setRegister pf undef;
      setRegister zf (zeroFlag v_5919);
      setRegister af undef;
      setRegister sf (bv_and (extract v_5915 0 1) (extract v_5908 0 1));
      setRegister cf (mux (notBool_ (eq v_5908 (expression.bv_nat 64 0))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_2959 : Mem) (v_2960 : reg (bv 64)) => do
      v_9608 <- evaluateAddress v_2959;
      v_9609 <- load v_9608 8;
      v_9616 <- eval (add (expression.bv_nat 64 1) (bv_xor v_9609 (mi (bitwidthMInt v_9609) -1)));
      v_9620 <- eval (bv_and v_9616 v_9609);
      setRegister (lhs.of_reg v_2960) v_9620;
      setRegister of (expression.bv_nat 1 0);
      setRegister pf undef;
      setRegister zf (zeroFlag v_9620);
      setRegister af undef;
      setRegister sf (bv_and (extract v_9616 0 1) (extract v_9609 0 1));
      setRegister cf (mux (notBool_ (eq v_9609 (expression.bv_nat 64 0))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end
