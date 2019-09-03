def cmpxchg8b1 : instruction :=
  definst "cmpxchg8b" $ do
    pattern fun (v_2435 : Mem) => do
      v_9395 <- evaluateAddress v_2435;
      v_9396 <- getRegister rdx;
      v_9398 <- getRegister rax;
      v_9401 <- load v_9395 8;
      v_9402 <- eval (eq (concat (extract v_9396 32 64) (extract v_9398 32 64)) v_9401);
      v_9403 <- getRegister rcx;
      store v_9395 (mux v_9402 (concat (extract v_9403 32 64) (extract v_9395 32 64)) v_9401) 8;
      setRegister rdx (mux v_9402 v_9396 (concat (expression.bv_nat 32 0) (extract v_9401 0 32)));
      setRegister rax (mux v_9402 v_9398 (concat (expression.bv_nat 32 0) (extract v_9401 32 64)));
      setRegister zf (mux v_9402 (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end
