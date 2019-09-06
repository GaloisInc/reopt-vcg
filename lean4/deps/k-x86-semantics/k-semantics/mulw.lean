def mulw1 : instruction :=
  definst "mulw" $ do
    pattern fun (v_2858 : reg (bv 16)) => do
      v_4355 <- getRegister v_2858;
      v_4357 <- getRegister rax;
      v_4360 <- eval (mul (concat (expression.bv_nat 16 0) v_4355) (concat (expression.bv_nat 16 0) (extract v_4357 48 64)));
      v_4361 <- eval (extract v_4360 0 16);
      v_4363 <- eval (notBool_ (eq v_4361 (expression.bv_nat 16 0)));
      v_4364 <- getRegister rdx;
      setRegister rax (concat (extract v_4357 0 48) (extract v_4360 16 32));
      setRegister rdx (concat (extract v_4364 0 48) v_4361);
      setRegister af undef;
      setRegister cf v_4363;
      setRegister of v_4363;
      setRegister pf undef;
      setRegister sf undef;
      setRegister zf undef;
      pure ()
    pat_end;
    pattern fun (v_2855 : Mem) => do
      v_8911 <- evaluateAddress v_2855;
      v_8912 <- load v_8911 2;
      v_8914 <- getRegister rax;
      v_8917 <- eval (mul (concat (expression.bv_nat 16 0) v_8912) (concat (expression.bv_nat 16 0) (extract v_8914 48 64)));
      v_8918 <- eval (extract v_8917 0 16);
      v_8920 <- eval (notBool_ (eq v_8918 (expression.bv_nat 16 0)));
      v_8921 <- getRegister rdx;
      setRegister rax (concat (extract v_8914 0 48) (extract v_8917 16 32));
      setRegister rdx (concat (extract v_8921 0 48) v_8918);
      setRegister af undef;
      setRegister cf v_8920;
      setRegister of v_8920;
      setRegister pf undef;
      setRegister sf undef;
      setRegister zf undef;
      pure ()
    pat_end
