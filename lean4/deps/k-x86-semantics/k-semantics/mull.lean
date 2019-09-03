def mull1 : instruction :=
  definst "mull" $ do
    pattern fun (v_2732 : reg (bv 32)) => do
      v_4154 <- getRegister v_2732;
      v_4156 <- getRegister rax;
      v_4159 <- eval (mul (concat (expression.bv_nat 32 0) v_4154) (concat (expression.bv_nat 32 0) (extract v_4156 32 64)));
      v_4160 <- eval (extract v_4159 0 32);
      v_4163 <- eval (mux (notBool_ (eq v_4160 (expression.bv_nat 32 0))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister edx v_4160;
      setRegister eax (extract v_4159 32 64);
      setRegister of v_4163;
      setRegister zf undef;
      setRegister pf undef;
      setRegister af undef;
      setRegister sf undef;
      setRegister cf v_4163;
      pure ()
    pat_end;
    pattern fun (v_2729 : Mem) => do
      v_8914 <- evaluateAddress v_2729;
      v_8915 <- load v_8914 4;
      v_8917 <- getRegister rax;
      v_8920 <- eval (mul (concat (expression.bv_nat 32 0) v_8915) (concat (expression.bv_nat 32 0) (extract v_8917 32 64)));
      v_8921 <- eval (extract v_8920 0 32);
      v_8924 <- eval (mux (notBool_ (eq v_8921 (expression.bv_nat 32 0))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister edx v_8921;
      setRegister eax (extract v_8920 32 64);
      setRegister of v_8924;
      setRegister zf undef;
      setRegister pf undef;
      setRegister af undef;
      setRegister sf undef;
      setRegister cf v_8924;
      pure ()
    pat_end
