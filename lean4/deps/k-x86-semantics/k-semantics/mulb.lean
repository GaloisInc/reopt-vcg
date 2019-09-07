def mulb1 : instruction :=
  definst "mulb" $ do
    pattern fun (mem_0 : Mem) => do
      v_1 <- evaluateAddress mem_0;
      v_2 <- load v_1 1;
      v_3 <- getRegister rax;
      v_4 <- eval (mul (concat (expression.bv_nat 8 0) v_2) (concat (expression.bv_nat 8 0) (extract v_3 56 64)));
      v_5 <- eval (notBool_ (eq (extract v_4 0 8) (expression.bv_nat 8 0)));
      setRegister rax (concat (extract v_3 0 48) v_4);
      setRegister af undef;
      setRegister cf v_5;
      setRegister of v_5;
      setRegister pf undef;
      setRegister sf undef;
      setRegister zf undef;
      pure ()
    pat_end;
    pattern fun (rh_0 : reg (bv 8)) => do
      v_1 <- getRegister rh_0;
      v_2 <- getRegister rax;
      v_3 <- eval (mul (concat (expression.bv_nat 8 0) v_1) (concat (expression.bv_nat 8 0) (extract v_2 56 64)));
      v_4 <- eval (notBool_ (eq (extract v_3 0 8) (expression.bv_nat 8 0)));
      setRegister rax (concat (extract v_2 0 48) v_3);
      setRegister af undef;
      setRegister cf v_4;
      setRegister of v_4;
      setRegister pf undef;
      setRegister sf undef;
      setRegister zf undef;
      pure ()
    pat_end
