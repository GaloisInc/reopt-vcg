def mulw1 : instruction :=
  definst "mulw" $ do
    pattern fun (v_2782 : reg (bv 16)) => do
      v_4377 <- getRegister v_2782;
      v_4379 <- getRegister rax;
      v_4382 <- eval (mul (concat (expression.bv_nat 16 0) v_4377) (concat (expression.bv_nat 16 0) (extract v_4379 48 64)));
      v_4383 <- eval (extract v_4382 0 16);
      v_4386 <- eval (mux (notBool_ (eq v_4383 (expression.bv_nat 16 0))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      v_4390 <- getRegister rdx;
      setRegister rdx (concat (extract v_4390 0 48) v_4383);
      setRegister rax (concat (extract v_4379 0 48) (extract v_4382 16 32));
      setRegister of v_4386;
      setRegister zf undef;
      setRegister pf undef;
      setRegister af undef;
      setRegister sf undef;
      setRegister cf v_4386;
      pure ()
    pat_end;
    pattern fun (v_2779 : Mem) => do
      v_9119 <- evaluateAddress v_2779;
      v_9120 <- load v_9119 2;
      v_9122 <- getRegister rax;
      v_9125 <- eval (mul (concat (expression.bv_nat 16 0) v_9120) (concat (expression.bv_nat 16 0) (extract v_9122 48 64)));
      v_9126 <- eval (extract v_9125 0 16);
      v_9129 <- eval (mux (notBool_ (eq v_9126 (expression.bv_nat 16 0))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      v_9133 <- getRegister rdx;
      setRegister rdx (concat (extract v_9133 0 48) v_9126);
      setRegister rax (concat (extract v_9122 0 48) (extract v_9125 16 32));
      setRegister of v_9129;
      setRegister zf undef;
      setRegister pf undef;
      setRegister af undef;
      setRegister sf undef;
      setRegister cf v_9129;
      pure ()
    pat_end
