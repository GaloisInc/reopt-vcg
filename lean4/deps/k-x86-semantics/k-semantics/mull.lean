def mull1 : instruction :=
  definst "mull" $ do
    pattern fun (v_2720 : reg (bv 32)) => do
      v_4141 <- getRegister v_2720;
      v_4143 <- getRegister rax;
      v_4146 <- eval (mul (concat (expression.bv_nat 32 0) v_4141) (concat (expression.bv_nat 32 0) (extract v_4143 32 64)));
      v_4147 <- eval (extract v_4146 0 32);
      v_4150 <- eval (mux (notBool_ (eq v_4147 (expression.bv_nat 32 0))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister edx v_4147;
      setRegister eax (extract v_4146 32 64);
      setRegister of v_4150;
      setRegister zf undef;
      setRegister pf undef;
      setRegister af undef;
      setRegister sf undef;
      setRegister cf v_4150;
      pure ()
    pat_end;
    pattern fun (v_2716 : Mem) => do
      v_8935 <- evaluateAddress v_2716;
      v_8936 <- load v_8935 4;
      v_8938 <- getRegister rax;
      v_8941 <- eval (mul (concat (expression.bv_nat 32 0) v_8936) (concat (expression.bv_nat 32 0) (extract v_8938 32 64)));
      v_8942 <- eval (extract v_8941 0 32);
      v_8945 <- eval (mux (notBool_ (eq v_8942 (expression.bv_nat 32 0))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister edx v_8942;
      setRegister eax (extract v_8941 32 64);
      setRegister of v_8945;
      setRegister zf undef;
      setRegister pf undef;
      setRegister af undef;
      setRegister sf undef;
      setRegister cf v_8945;
      pure ()
    pat_end
