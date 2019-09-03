def mulq1 : instruction :=
  definst "mulq" $ do
    pattern fun (v_2745 : reg (bv 64)) => do
      v_4217 <- getRegister v_2745;
      v_4219 <- getRegister rax;
      v_4221 <- eval (mul (concat (expression.bv_nat 64 0) v_4217) (concat (expression.bv_nat 64 0) v_4219));
      v_4222 <- eval (extract v_4221 0 64);
      v_4225 <- eval (mux (notBool_ (eq v_4222 (expression.bv_nat 64 0))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister rdx v_4222;
      setRegister rax (extract v_4221 64 128);
      setRegister of v_4225;
      setRegister zf undef;
      setRegister pf undef;
      setRegister af undef;
      setRegister sf undef;
      setRegister cf v_4225;
      pure ()
    pat_end;
    pattern fun (v_2741 : Mem) => do
      v_9003 <- evaluateAddress v_2741;
      v_9004 <- load v_9003 8;
      v_9006 <- getRegister rax;
      v_9008 <- eval (mul (concat (expression.bv_nat 64 0) v_9004) (concat (expression.bv_nat 64 0) v_9006));
      v_9009 <- eval (extract v_9008 0 64);
      v_9012 <- eval (mux (notBool_ (eq v_9009 (expression.bv_nat 64 0))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister rdx v_9009;
      setRegister rax (extract v_9008 64 128);
      setRegister of v_9012;
      setRegister zf undef;
      setRegister pf undef;
      setRegister af undef;
      setRegister sf undef;
      setRegister cf v_9012;
      pure ()
    pat_end
