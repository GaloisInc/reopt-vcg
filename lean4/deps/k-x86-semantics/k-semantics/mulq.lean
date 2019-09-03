def mulq1 : instruction :=
  definst "mulq" $ do
    pattern fun (v_2757 : reg (bv 64)) => do
      v_4302 <- getRegister v_2757;
      v_4304 <- getRegister rax;
      v_4306 <- eval (mul (concat (expression.bv_nat 64 0) v_4302) (concat (expression.bv_nat 64 0) v_4304));
      v_4307 <- eval (extract v_4306 0 64);
      v_4310 <- eval (mux (notBool_ (eq v_4307 (expression.bv_nat 64 0))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister rdx v_4307;
      setRegister rax (extract v_4306 64 128);
      setRegister of v_4310;
      setRegister zf undef;
      setRegister pf undef;
      setRegister af undef;
      setRegister sf undef;
      setRegister cf v_4310;
      pure ()
    pat_end;
    pattern fun (v_2754 : Mem) => do
      v_9054 <- evaluateAddress v_2754;
      v_9055 <- load v_9054 8;
      v_9057 <- getRegister rax;
      v_9059 <- eval (mul (concat (expression.bv_nat 64 0) v_9055) (concat (expression.bv_nat 64 0) v_9057));
      v_9060 <- eval (extract v_9059 0 64);
      v_9063 <- eval (mux (notBool_ (eq v_9060 (expression.bv_nat 64 0))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister rdx v_9060;
      setRegister rax (extract v_9059 64 128);
      setRegister of v_9063;
      setRegister zf undef;
      setRegister pf undef;
      setRegister af undef;
      setRegister sf undef;
      setRegister cf v_9063;
      pure ()
    pat_end
