def cmpxchg8b1 : instruction :=
  definst "cmpxchg8b" $ do
    pattern fun (v_2526 : Mem) => do
      v_9044 <- evaluateAddress v_2526;
      v_9045 <- getRegister rdx;
      v_9047 <- getRegister rax;
      v_9050 <- load v_9044 8;
      v_9051 <- eval (eq (concat (extract v_9045 32 64) (extract v_9047 32 64)) v_9050);
      v_9052 <- getRegister rcx;
      store v_9044 (mux v_9051 (concat (extract v_9052 32 64) (extract v_9044 32 64)) v_9050) 8;
      setRegister rax (mux v_9051 v_9047 (concat (expression.bv_nat 32 0) (extract v_9050 32 64)));
      setRegister rdx (mux v_9051 v_9045 (concat (expression.bv_nat 32 0) (extract v_9050 0 32)));
      setRegister zf v_9051;
      pure ()
    pat_end
