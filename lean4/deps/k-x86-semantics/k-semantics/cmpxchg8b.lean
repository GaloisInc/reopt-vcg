def cmpxchg8b1 : instruction :=
  definst "cmpxchg8b" $ do
    pattern fun (v_2499 : Mem) => do
      v_9034 <- evaluateAddress v_2499;
      v_9035 <- getRegister rdx;
      v_9037 <- getRegister rax;
      v_9040 <- load v_9034 8;
      v_9041 <- eval (eq (concat (extract v_9035 32 64) (extract v_9037 32 64)) v_9040);
      v_9042 <- getRegister rcx;
      store v_9034 (mux v_9041 (concat (extract v_9042 32 64) (extract v_9034 32 64)) v_9040) 8;
      setRegister rdx (mux v_9041 v_9035 (concat (expression.bv_nat 32 0) (extract v_9040 0 32)));
      setRegister rax (mux v_9041 v_9037 (concat (expression.bv_nat 32 0) (extract v_9040 32 64)));
      setRegister zf v_9041;
      pure ()
    pat_end
