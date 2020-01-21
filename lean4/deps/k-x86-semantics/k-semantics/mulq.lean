def mulq : instruction :=
  definst "mulq" $ do
    pattern fun (mem_0 : Mem) => do
      v_1 <- evaluateAddress mem_0;
      v_2 <- load v_1 8;
      v_3 <- getRegister rax;
      v_4 <- eval (mul (concat (expression.bv_nat 64 0) v_2) (concat (expression.bv_nat 64 0) v_3));
      v_5 <- eval (extract v_4 0 64);
      v_6 <- eval (notBool_ (eq v_5 (expression.bv_nat 64 0)));
      setRegister rax (extract v_4 64 128);
      setRegister rdx v_5;
      setRegister af undef;
      setRegister cf v_6;
      setRegister of v_6;
      setRegister pf undef;
      setRegister sf undef;
      setRegister zf undef;
      pure ()
    pat_end;
    pattern fun (r64_0 : reg (bv 64)) => do
      v_1 <- getRegister (lhs.of_reg r64_0);
      v_2 <- getRegister rax;
      v_3 <- eval (mul (concat (expression.bv_nat 64 0) v_1) (concat (expression.bv_nat 64 0) v_2));
      v_4 <- eval (extract v_3 0 64);
      v_5 <- eval (notBool_ (eq v_4 (expression.bv_nat 64 0)));
      setRegister rax (extract v_3 64 128);
      setRegister rdx v_4;
      setRegister af undef;
      setRegister cf v_5;
      setRegister of v_5;
      setRegister pf undef;
      setRegister sf undef;
      setRegister zf undef;
      pure ()
    pat_end
