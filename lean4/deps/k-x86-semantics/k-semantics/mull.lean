def mull1 : instruction :=
  definst "mull" $ do
    pattern fun (mem_0 : Mem) => do
      v_1 <- evaluateAddress mem_0;
      v_2 <- load v_1 4;
      v_3 <- getRegister rax;
      v_4 <- eval (mul (concat (expression.bv_nat 32 0) v_2) (concat (expression.bv_nat 32 0) (extract v_3 32 64)));
      v_5 <- eval (extract v_4 0 32);
      v_6 <- eval (notBool_ (eq v_5 (expression.bv_nat 32 0)));
      setRegister eax (extract v_4 32 64);
      setRegister edx v_5;
      setRegister af undef;
      setRegister cf v_6;
      setRegister of v_6;
      setRegister pf undef;
      setRegister sf undef;
      setRegister zf undef;
      pure ()
    pat_end;
    pattern fun (r32_0 : reg (bv 32)) => do
      v_1 <- getRegister r32_0;
      v_2 <- getRegister rax;
      v_3 <- eval (mul (concat (expression.bv_nat 32 0) v_1) (concat (expression.bv_nat 32 0) (extract v_2 32 64)));
      v_4 <- eval (extract v_3 0 32);
      v_5 <- eval (notBool_ (eq v_4 (expression.bv_nat 32 0)));
      setRegister eax (extract v_3 32 64);
      setRegister edx v_4;
      setRegister af undef;
      setRegister cf v_5;
      setRegister of v_5;
      setRegister pf undef;
      setRegister sf undef;
      setRegister zf undef;
      pure ()
    pat_end
