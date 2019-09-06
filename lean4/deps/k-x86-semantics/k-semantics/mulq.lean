def mulq1 : instruction :=
  definst "mulq" $ do
    pattern fun (v_2833 : reg (bv 64)) => do
      v_4305 <- getRegister v_2833;
      v_4307 <- getRegister rax;
      v_4309 <- eval (mul (concat (expression.bv_nat 64 0) v_4305) (concat (expression.bv_nat 64 0) v_4307));
      v_4310 <- eval (extract v_4309 0 64);
      v_4312 <- eval (notBool_ (eq v_4310 (expression.bv_nat 64 0)));
      setRegister rax (extract v_4309 64 128);
      setRegister rdx v_4310;
      setRegister af undef;
      setRegister cf v_4312;
      setRegister of v_4312;
      setRegister pf undef;
      setRegister sf undef;
      setRegister zf undef;
      pure ()
    pat_end;
    pattern fun (v_2830 : Mem) => do
      v_8871 <- evaluateAddress v_2830;
      v_8872 <- load v_8871 8;
      v_8874 <- getRegister rax;
      v_8876 <- eval (mul (concat (expression.bv_nat 64 0) v_8872) (concat (expression.bv_nat 64 0) v_8874));
      v_8877 <- eval (extract v_8876 0 64);
      v_8879 <- eval (notBool_ (eq v_8877 (expression.bv_nat 64 0)));
      setRegister rax (extract v_8876 64 128);
      setRegister rdx v_8877;
      setRegister af undef;
      setRegister cf v_8879;
      setRegister of v_8879;
      setRegister pf undef;
      setRegister sf undef;
      setRegister zf undef;
      pure ()
    pat_end
