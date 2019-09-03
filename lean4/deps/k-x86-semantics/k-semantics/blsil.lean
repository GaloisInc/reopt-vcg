def blsil1 : instruction :=
  definst "blsil" $ do
    pattern fun (v_2968 : reg (bv 32)) (v_2969 : reg (bv 32)) => do
      v_6043 <- getRegister v_2968;
      v_6048 <- eval (add (expression.bv_nat 32 1) (bv_xor v_6043 (expression.bv_nat 32 4294967295)));
      v_6052 <- eval (bv_and v_6048 v_6043);
      setRegister (lhs.of_reg v_2969) v_6052;
      setRegister of (expression.bv_nat 1 0);
      setRegister pf undef;
      setRegister zf (zeroFlag v_6052);
      setRegister af undef;
      setRegister sf (bv_and (extract v_6048 0 1) (extract v_6043 0 1));
      setRegister cf (mux (notBool_ (eq v_6043 (expression.bv_nat 32 0))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_2963 : Mem) (v_2964 : reg (bv 32)) => do
      v_9879 <- evaluateAddress v_2963;
      v_9880 <- load v_9879 4;
      v_9885 <- eval (add (expression.bv_nat 32 1) (bv_xor v_9880 (expression.bv_nat 32 4294967295)));
      v_9889 <- eval (bv_and v_9885 v_9880);
      setRegister (lhs.of_reg v_2964) v_9889;
      setRegister of (expression.bv_nat 1 0);
      setRegister pf undef;
      setRegister af undef;
      setRegister zf (zeroFlag v_9889);
      setRegister sf (bv_and (extract v_9885 0 1) (extract v_9880 0 1));
      setRegister cf (mux (notBool_ (eq v_9880 (expression.bv_nat 32 0))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end
