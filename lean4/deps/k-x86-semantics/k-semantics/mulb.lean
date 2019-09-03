def mulb1 : instruction :=
  definst "mulb" $ do
    pattern fun (v_2721 : reg (bv 8)) => do
      v_4113 <- getRegister v_2721;
      v_4115 <- getRegister rax;
      v_4118 <- eval (mul (concat (expression.bv_nat 8 0) v_4113) (concat (expression.bv_nat 8 0) (extract v_4115 56 64)));
      v_4122 <- eval (mux (notBool_ (eq (extract v_4118 0 8) (expression.bv_nat 8 0))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister rax (concat (extract v_4115 0 48) v_4118);
      setRegister of v_4122;
      setRegister pf undef;
      setRegister zf undef;
      setRegister af undef;
      setRegister sf undef;
      setRegister cf v_4122;
      pure ()
    pat_end;
    pattern fun (v_2718 : Mem) => do
      v_8894 <- evaluateAddress v_2718;
      v_8895 <- load v_8894 1;
      v_8897 <- getRegister rax;
      v_8900 <- eval (mul (concat (expression.bv_nat 8 0) v_8895) (concat (expression.bv_nat 8 0) (extract v_8897 56 64)));
      v_8904 <- eval (mux (notBool_ (eq (extract v_8900 0 8) (expression.bv_nat 8 0))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister rax (concat (extract v_8897 0 48) v_8900);
      setRegister of v_8904;
      setRegister pf undef;
      setRegister zf undef;
      setRegister af undef;
      setRegister sf undef;
      setRegister cf v_8904;
      pure ()
    pat_end
