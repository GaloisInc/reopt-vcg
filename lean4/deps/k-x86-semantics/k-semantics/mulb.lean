def mulb1 : instruction :=
  definst "mulb" $ do
    pattern fun (v_2709 : reg (bv 8)) => do
      v_4100 <- getRegister v_2709;
      v_4102 <- getRegister rax;
      v_4105 <- eval (mul (concat (expression.bv_nat 8 0) v_4100) (concat (expression.bv_nat 8 0) (extract v_4102 56 64)));
      v_4109 <- eval (mux (notBool_ (eq (extract v_4105 0 8) (expression.bv_nat 8 0))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister rax (concat (extract v_4102 0 48) v_4105);
      setRegister of v_4109;
      setRegister pf undef;
      setRegister zf undef;
      setRegister af undef;
      setRegister sf undef;
      setRegister cf v_4109;
      pure ()
    pat_end;
    pattern fun (v_2705 : Mem) => do
      v_8915 <- evaluateAddress v_2705;
      v_8916 <- load v_8915 1;
      v_8918 <- getRegister rax;
      v_8921 <- eval (mul (concat (expression.bv_nat 8 0) v_8916) (concat (expression.bv_nat 8 0) (extract v_8918 56 64)));
      v_8925 <- eval (mux (notBool_ (eq (extract v_8921 0 8) (expression.bv_nat 8 0))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister rax (concat (extract v_8918 0 48) v_8921);
      setRegister of v_8925;
      setRegister pf undef;
      setRegister zf undef;
      setRegister af undef;
      setRegister sf undef;
      setRegister cf v_8925;
      pure ()
    pat_end
