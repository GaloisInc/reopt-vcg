def mulq1 : instruction :=
  definst "mulq" $ do
    pattern fun (v_2807 : reg (bv 64)) => do
      v_4278 <- getRegister v_2807;
      v_4280 <- getRegister rax;
      v_4282 <- eval (mul (concat (expression.bv_nat 64 0) v_4278) (concat (expression.bv_nat 64 0) v_4280));
      v_4283 <- eval (extract v_4282 0 64);
      v_4285 <- eval (notBool_ (eq v_4283 (expression.bv_nat 64 0)));
      setRegister rdx v_4283;
      setRegister rax (extract v_4282 64 128);
      setRegister af undef;
      setRegister cf v_4285;
      setRegister of v_4285;
      setRegister pf undef;
      setRegister sf undef;
      setRegister zf undef;
      pure ()
    pat_end;
    pattern fun (v_2804 : Mem) => do
      v_8844 <- evaluateAddress v_2804;
      v_8845 <- load v_8844 8;
      v_8847 <- getRegister rax;
      v_8849 <- eval (mul (concat (expression.bv_nat 64 0) v_8845) (concat (expression.bv_nat 64 0) v_8847));
      v_8850 <- eval (extract v_8849 0 64);
      v_8852 <- eval (notBool_ (eq v_8850 (expression.bv_nat 64 0)));
      setRegister rdx v_8850;
      setRegister rax (extract v_8849 64 128);
      setRegister af undef;
      setRegister cf v_8852;
      setRegister of v_8852;
      setRegister pf undef;
      setRegister sf undef;
      setRegister zf undef;
      pure ()
    pat_end
