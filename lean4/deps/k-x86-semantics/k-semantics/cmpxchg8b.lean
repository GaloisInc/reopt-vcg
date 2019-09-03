def cmpxchg8b1 : instruction :=
  definst "cmpxchg8b" $ do
    pattern fun (v_2446 : Mem) => do
      v_9985 <- evaluateAddress v_2446;
      v_9986 <- getRegister rdx;
      v_9988 <- getRegister rax;
      v_9991 <- load v_9985 8;
      v_9992 <- eval (eq (concat (extract v_9986 32 64) (extract v_9988 32 64)) v_9991);
      v_9993 <- getRegister rcx;
      store v_9985 (mux v_9992 (concat (extract v_9993 32 64) (extract v_9985 32 64)) v_9991) 8;
      setRegister rdx (mux v_9992 v_9986 (concat (expression.bv_nat 32 0) (extract v_9991 0 32)));
      setRegister rax (mux v_9992 v_9988 (concat (expression.bv_nat 32 0) (extract v_9991 32 64)));
      setRegister zf (mux v_9992 (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end
