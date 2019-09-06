def mulb1 : instruction :=
  definst "mulb" $ do
    pattern fun (v_2801 : reg (bv 8)) => do
      v_4209 <- getRegister v_2801;
      v_4211 <- getRegister rax;
      v_4214 <- eval (mul (concat (expression.bv_nat 8 0) v_4209) (concat (expression.bv_nat 8 0) (extract v_4211 56 64)));
      v_4217 <- eval (notBool_ (eq (extract v_4214 0 8) (expression.bv_nat 8 0)));
      setRegister rax (concat (extract v_4211 0 48) v_4214);
      setRegister af undef;
      setRegister cf v_4217;
      setRegister of v_4217;
      setRegister pf undef;
      setRegister sf undef;
      setRegister zf undef;
      pure ()
    pat_end;
    pattern fun (v_2794 : Mem) => do
      v_8785 <- evaluateAddress v_2794;
      v_8786 <- load v_8785 1;
      v_8788 <- getRegister rax;
      v_8791 <- eval (mul (concat (expression.bv_nat 8 0) v_8786) (concat (expression.bv_nat 8 0) (extract v_8788 56 64)));
      v_8794 <- eval (notBool_ (eq (extract v_8791 0 8) (expression.bv_nat 8 0)));
      setRegister rax (concat (extract v_8788 0 48) v_8791);
      setRegister af undef;
      setRegister cf v_8794;
      setRegister of v_8794;
      setRegister pf undef;
      setRegister sf undef;
      setRegister zf undef;
      pure ()
    pat_end
