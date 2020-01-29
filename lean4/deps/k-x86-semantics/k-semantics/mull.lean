def mull : instruction :=
  definst "mull" $ do
    pattern fun (mem_0 : Mem) => do
      v_1 <- evaluateAddress mem_0;
      v_2 <- load v_1 4;
      v_3 <- getRegister rax;
      (v_4 : expression (bv 32)) <- eval (extract v_3 32 64);
      v_5 <- eval (mul (concat (expression.bv_nat 32 0) v_2) (concat (expression.bv_nat 32 0) v_4));
      (v_6 : expression (bv 32)) <- eval (extract v_5 0 32);
      v_7 <- eval (notBool_ (eq v_6 (expression.bv_nat 32 0)));
      (v_8 : expression (bv 32)) <- eval (extract v_5 32 64);
      setRegister eax v_8;
      setRegister edx v_6;
      setRegister af undef;
      setRegister cf v_7;
      setRegister of v_7;
      setRegister pf undef;
      setRegister sf undef;
      setRegister zf undef;
      pure ()
    pat_end;
    pattern fun (r32_0 : reg (bv 32)) => do
      v_1 <- getRegister (lhs.of_reg r32_0);
      v_2 <- getRegister rax;
      (v_3 : expression (bv 32)) <- eval (extract v_2 32 64);
      v_4 <- eval (mul (concat (expression.bv_nat 32 0) v_1) (concat (expression.bv_nat 32 0) v_3));
      (v_5 : expression (bv 32)) <- eval (extract v_4 0 32);
      v_6 <- eval (notBool_ (eq v_5 (expression.bv_nat 32 0)));
      (v_7 : expression (bv 32)) <- eval (extract v_4 32 64);
      setRegister eax v_7;
      setRegister edx v_5;
      setRegister af undef;
      setRegister cf v_6;
      setRegister of v_6;
      setRegister pf undef;
      setRegister sf undef;
      setRegister zf undef;
      pure ()
    pat_end
