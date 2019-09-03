def blsil1 : instruction :=
  definst "blsil" $ do
    pattern fun (v_2955 : reg (bv 32)) (v_2956 : reg (bv 32)) => do
      v_5884 <- getRegister v_2955;
      v_5891 <- eval (add (expression.bv_nat 32 1) (bv_xor v_5884 (mi (bitwidthMInt v_5884) -1)));
      v_5895 <- eval (bv_and v_5891 v_5884);
      setRegister (lhs.of_reg v_2956) v_5895;
      setRegister of (expression.bv_nat 1 0);
      setRegister pf undef;
      setRegister af undef;
      setRegister zf (zeroFlag v_5895);
      setRegister sf (bv_and (extract v_5891 0 1) (extract v_5884 0 1));
      setRegister cf (mux (notBool_ (eq v_5884 (expression.bv_nat 32 0))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_2950 : Mem) (v_2951 : reg (bv 32)) => do
      v_9587 <- evaluateAddress v_2950;
      v_9588 <- load v_9587 4;
      v_9595 <- eval (add (expression.bv_nat 32 1) (bv_xor v_9588 (mi (bitwidthMInt v_9588) -1)));
      v_9599 <- eval (bv_and v_9595 v_9588);
      setRegister (lhs.of_reg v_2951) v_9599;
      setRegister of (expression.bv_nat 1 0);
      setRegister pf undef;
      setRegister af undef;
      setRegister zf (zeroFlag v_9599);
      setRegister sf (bv_and (extract v_9595 0 1) (extract v_9588 0 1));
      setRegister cf (mux (notBool_ (eq v_9588 (expression.bv_nat 32 0))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end
