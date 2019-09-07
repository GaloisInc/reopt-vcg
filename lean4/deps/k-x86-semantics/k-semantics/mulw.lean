def mulw1 : instruction :=
  definst "mulw" $ do
    pattern fun (mem_0 : Mem) => do
      v_1 <- evaluateAddress mem_0;
      v_2 <- load v_1 2;
      v_3 <- getRegister rax;
      v_4 <- eval (mul (concat (expression.bv_nat 16 0) v_2) (concat (expression.bv_nat 16 0) (extract v_3 48 64)));
      v_5 <- eval (extract v_4 0 16);
      v_6 <- eval (notBool_ (eq v_5 (expression.bv_nat 16 0)));
      v_7 <- getRegister rdx;
      setRegister rax (concat (extract v_3 0 48) (extract v_4 16 32));
      setRegister rdx (concat (extract v_7 0 48) v_5);
      setRegister af undef;
      setRegister cf v_6;
      setRegister of v_6;
      setRegister pf undef;
      setRegister sf undef;
      setRegister zf undef;
      pure ()
    pat_end;
    pattern fun (r16_0 : reg (bv 16)) => do
      v_1 <- getRegister r16_0;
      v_2 <- getRegister rax;
      v_3 <- eval (mul (concat (expression.bv_nat 16 0) v_1) (concat (expression.bv_nat 16 0) (extract v_2 48 64)));
      v_4 <- eval (extract v_3 0 16);
      v_5 <- eval (notBool_ (eq v_4 (expression.bv_nat 16 0)));
      v_6 <- getRegister rdx;
      setRegister rax (concat (extract v_2 0 48) (extract v_3 16 32));
      setRegister rdx (concat (extract v_6 0 48) v_4);
      setRegister af undef;
      setRegister cf v_5;
      setRegister of v_5;
      setRegister pf undef;
      setRegister sf undef;
      setRegister zf undef;
      pure ()
    pat_end
