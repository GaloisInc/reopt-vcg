def blsmskl1 : instruction :=
  definst "blsmskl" $ do
    pattern fun (v_2973 : reg (bv 32)) (v_2974 : reg (bv 32)) => do
      v_5932 <- getRegister v_2973;
      v_5935 <- eval (sub v_5932 (expression.bv_nat 32 1));
      setRegister (lhs.of_reg v_2974) (bv_xor v_5935 v_5932);
      setRegister of (expression.bv_nat 1 0);
      setRegister pf undef;
      setRegister af undef;
      setRegister zf (expression.bv_nat 1 0);
      setRegister sf (bv_xor (extract v_5935 0 1) (extract v_5932 0 1));
      setRegister cf (mux (eq v_5932 (expression.bv_nat 32 0)) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_2968 : Mem) (v_2969 : reg (bv 32)) => do
      v_9629 <- evaluateAddress v_2968;
      v_9630 <- load v_9629 4;
      v_9633 <- eval (sub v_9630 (expression.bv_nat 32 1));
      setRegister (lhs.of_reg v_2969) (bv_xor v_9633 v_9630);
      setRegister of (expression.bv_nat 1 0);
      setRegister pf undef;
      setRegister zf (expression.bv_nat 1 0);
      setRegister af undef;
      setRegister sf (bv_xor (extract v_9633 0 1) (extract v_9630 0 1));
      setRegister cf (mux (eq v_9630 (expression.bv_nat 32 0)) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end
