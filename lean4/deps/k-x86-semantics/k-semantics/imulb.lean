def imulb1 : instruction :=
  definst "imulb" $ do
    pattern fun (v_2892 : reg (bv 8)) => do
      v_5320 <- getRegister v_2892;
      v_5322 <- getRegister rax;
      v_5325 <- eval (mul (leanSignExtend v_5320 16) (leanSignExtend (extract v_5322 56 64) 16));
      v_5330 <- eval (mux (notBool_ (eq v_5325 (leanSignExtend (extract v_5325 8 16) 16))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister rax (concat (extract v_5322 0 48) v_5325);
      setRegister of v_5330;
      setRegister pf undef;
      setRegister zf undef;
      setRegister af undef;
      setRegister sf undef;
      setRegister cf v_5330;
      pure ()
    pat_end;
    pattern fun (v_2889 : Mem) => do
      v_9268 <- evaluateAddress v_2889;
      v_9269 <- load v_9268 1;
      v_9271 <- getRegister rax;
      v_9274 <- eval (mul (leanSignExtend v_9269 16) (leanSignExtend (extract v_9271 56 64) 16));
      v_9279 <- eval (mux (notBool_ (eq v_9274 (leanSignExtend (extract v_9274 8 16) 16))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister rax (concat (extract v_9271 0 48) v_9274);
      setRegister of v_9279;
      setRegister pf undef;
      setRegister zf undef;
      setRegister af undef;
      setRegister sf undef;
      setRegister cf v_9279;
      pure ()
    pat_end
