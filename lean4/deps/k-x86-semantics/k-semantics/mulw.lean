def mulw1 : instruction :=
  definst "mulw" $ do
    pattern fun (v_2833 : reg (bv 16)) => do
      v_4328 <- getRegister v_2833;
      v_4330 <- getRegister rax;
      v_4333 <- eval (mul (concat (expression.bv_nat 16 0) v_4328) (concat (expression.bv_nat 16 0) (extract v_4330 48 64)));
      v_4334 <- eval (extract v_4333 0 16);
      v_4336 <- eval (notBool_ (eq v_4334 (expression.bv_nat 16 0)));
      v_4340 <- getRegister rdx;
      setRegister rdx (concat (extract v_4340 0 48) v_4334);
      setRegister rax (concat (extract v_4330 0 48) (extract v_4333 16 32));
      setRegister af undef;
      setRegister cf v_4336;
      setRegister of v_4336;
      setRegister pf undef;
      setRegister sf undef;
      setRegister zf undef;
      pure ()
    pat_end;
    pattern fun (v_2829 : Mem) => do
      v_8884 <- evaluateAddress v_2829;
      v_8885 <- load v_8884 2;
      v_8887 <- getRegister rax;
      v_8890 <- eval (mul (concat (expression.bv_nat 16 0) v_8885) (concat (expression.bv_nat 16 0) (extract v_8887 48 64)));
      v_8891 <- eval (extract v_8890 0 16);
      v_8893 <- eval (notBool_ (eq v_8891 (expression.bv_nat 16 0)));
      v_8897 <- getRegister rdx;
      setRegister rdx (concat (extract v_8897 0 48) v_8891);
      setRegister rax (concat (extract v_8887 0 48) (extract v_8890 16 32));
      setRegister af undef;
      setRegister cf v_8893;
      setRegister of v_8893;
      setRegister pf undef;
      setRegister sf undef;
      setRegister zf undef;
      pure ()
    pat_end
