def mull1 : instruction :=
  definst "mull" $ do
    pattern fun (v_2783 : reg (bv 32)) => do
      v_4203 <- getRegister v_2783;
      v_4205 <- getRegister rax;
      v_4208 <- eval (mul (concat (expression.bv_nat 32 0) v_4203) (concat (expression.bv_nat 32 0) (extract v_4205 32 64)));
      v_4209 <- eval (extract v_4208 0 32);
      v_4211 <- eval (notBool_ (eq v_4209 (expression.bv_nat 32 0)));
      setRegister edx v_4209;
      setRegister eax (extract v_4208 32 64);
      setRegister af undef;
      setRegister cf v_4211;
      setRegister of v_4211;
      setRegister pf undef;
      setRegister sf undef;
      setRegister zf undef;
      pure ()
    pat_end;
    pattern fun (v_2779 : Mem) => do
      v_8777 <- evaluateAddress v_2779;
      v_8778 <- load v_8777 4;
      v_8780 <- getRegister rax;
      v_8783 <- eval (mul (concat (expression.bv_nat 32 0) v_8778) (concat (expression.bv_nat 32 0) (extract v_8780 32 64)));
      v_8784 <- eval (extract v_8783 0 32);
      v_8786 <- eval (notBool_ (eq v_8784 (expression.bv_nat 32 0)));
      setRegister edx v_8784;
      setRegister eax (extract v_8783 32 64);
      setRegister af undef;
      setRegister cf v_8786;
      setRegister of v_8786;
      setRegister pf undef;
      setRegister sf undef;
      setRegister zf undef;
      pure ()
    pat_end
